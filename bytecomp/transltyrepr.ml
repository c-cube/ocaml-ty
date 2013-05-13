
open Misc
open Asttypes
open Lambda
open Path
open Typedtree
open Types

type error =
  | Dynamic_type of string * type_expr
  | Unanchored_type of Path.t

exception TyReprError of error
exception Error of Location.t * Types.type_expr * error

(** Primitives (byterun/ty.c) *)

let new_expr_id_prim =
  Pccall
    Primitive.(
      {prim_name = "caml_ty_new_expr_id"; prim_arity = 1; prim_alloc = false;
       prim_native_name = ""; prim_native_float = false})

let new_coercion_id_prim =
  Pccall
    Primitive.(
      {prim_name = "caml_ty_new_coercion_id"; prim_arity = 1; prim_alloc = false;
       prim_native_name = ""; prim_native_float = false})

let new_expr_id = Lprim(new_expr_id_prim, [lambda_unit])
let new_coercion_id = Lprim(new_coercion_id_prim, [lambda_unit])

(** Helpers *)

let make_array l = Lprim (Pmakearray Pgenarray, l)
let rec remove_first n l =
  if n <= 0 then l else remove_first (n-1) (List.tl l)
let ref_none = Lprim (Pmakeblock (0, Mutable), [lambda_unit])
let ref_some x = Lprim (Pmakeblock (0, Mutable),
                        [Lprim (Pmakeblock (0, Immutable), [x])])

(** Compilation of Camlinternal.dynpath *)

let dynpath_dot p name =
  (* CamlinternalTy.Pdot (p, name) *)
  Lprim(Pmakeblock (1, Immutable), [p; Lconst (Const_immstring name)])
let dynpath_apply p1 p2 =
  (* CamlinternalTy.Papply (p1, p2) *)
  Lprim(Pmakeblock (2, Immutable), [p1; p2])

let rec transl_dynpath env = function
  | Pident id ->
      if Ident.global id then
        if !Clflags.native_code
        then Lprim(Pfield 0, [Lprim (Pgetglobal (Ident.dynpath id), [])])
        else Lprim(Pgetglobal (Ident.dynpath id), [])
      else Lvar (Ident.dynpath id)
  | Pdot(p, name, _) -> dynpath_dot (transl_dynpath env p) name
  | Papply(p1, p2) ->
      dynpath_apply (transl_dynpath env p1) (transl_module_id env p2)

and transl_module_id env p =
  transl_dynpath env (Env.find_module_dynid p env)

let dynpath_new_anonymous_id =
  (* CamlinternalTy.Pident (new_module_id, Anonymous) *)
  Lprim(Pmakeblock (0, Immutable),
        [new_coercion_id; Lconst (Const_base (Const_int 0))])

let dynpath_new_compunit_id name =
  (* CamlinternalTy.Pident (new_module_id, Compunit name) *)
  Lprim(Pmakeblock (0, Immutable),
        [new_coercion_id;
         Lprim(Pmakeblock (0, Immutable),
               [Lconst (Const_immstring name)])])

let dynpath_new_coercion_id env parent =
  match parent with
  | Some path ->
      (* CamlinternalTy.Pident (new_module_id, Coercion path) *)
      Lprim(Pmakeblock (0, Immutable),
            [new_coercion_id;
             Lprim(Pmakeblock (1, Immutable),
                   [transl_dynpath env path])])
  | None -> dynpath_new_anonymous_id

let rec transl_module_dynpath mexp =
  match mexp.mod_desc with
  | Tmod_ident (p,_) -> transl_module_id mexp.mod_env p
  | Tmod_apply(funct, arg, coercion) when !Clflags.applicative_functors ->
      dynpath_apply
        (transl_module_dynpath funct)
        (transl_module_dynpath arg)
  | _ -> dynpath_new_anonymous_id

let transl_dynpath_init ids =
  make_sequence (fun id ->
    let name = Ident.name id in
    Lambda.Lprim(Lambda.Psetglobal (Ident.dynpath id),
                  [dynpath_new_compunit_id name]))
    ids

let transl_dynpath_init_pack targetname names =
  let id = Ident.create_persistent targetname in
  make_sequence (fun name ->
    let fullname = targetname ^ "." ^ name in
    let modid = Ident.create_persistent fullname in
    Lambda.Lprim(Lambda.Psetglobal (Ident.dynpath modid),
                 [transl_dynpath Env.empty (Pdot (Pident id, name, nopos))]))
    names

(** When [ty] is the return type of a gadt constructor and [tys] the
    types of its paramaters, then [gadt_variables ty tys] computes a
    pair (fv, ev) where [fv] is the list of free variables that
    appears in [ty] and [ev] the list of 'existentials variable' in
    [tys] (i.e. fv(ty)\fv(tys)). *)

let gadt_variables ty tys =
  (* cf. Daterepr.constructor_descrs pour faire plus simple... *)
  let module TypeSet = Btype.TypeSet in
  let rec unique s = function
    | [] -> (s, [])
    | t::q when not (TypeSet.mem t s) ->
        let (s, r) = unique (TypeSet.add t s) q in
        (s, t::r)
    | _::q -> unique s q in
  let (fv_set, free_vars_ty) = unique TypeSet.empty (Ctype.free_variables ty) in
  let (_,free_vars_tys) =
    List.fold_right
      (fun ty (s, acc) ->
        let s, r = unique s (Ctype.free_variables ty) in (s, r @ acc))
      tys (fv_set,[]) in
  (free_vars_ty, free_vars_tys)

let is_gadt kind =
  match kind with
  | Type_variant cases ->
      List.exists (fun (_, _, ret) -> ret <> None) cases
  | Type_record _ | Type_abstract -> false

(** Detection of physical sharing in type expression.

    The collected 'shared_expr', 'known_decl' and 'aliases' will be
    compiled in a single Lletrec (Cf. build_context). *)

type context = {
  mutable env: Env.t;
  loc: Location.t;
  mutable known_expr: type_expr list;
  mutable shared_expr: (Types.type_expr * (Ident.t * Env.t)) list;
  mutable known_decl: (Path.t * (Ident.t * Env.t)) list;
  mutable aliases:
    (Typedtree.core_type * (Ident.t * Typedtree.core_type)) list;
  mutable alias_vars: (string * Ident.t) list;
}

let create_context env loc =
  { env; loc;
    known_expr = []; shared_expr = [];
    known_decl = [];
    aliases = []; alias_vars = [] }

let get_row_fields row =
  let row = Btype.row_repr row in
  let fields =
    if row.row_closed then
      List.filter (fun (_, f) -> Btype.row_field_repr f <> Rabsent)
        row.row_fields
    else row.row_fields in
  let present =
    List.filter
      (fun (_, f) ->
        match Btype.row_field_repr f with
        | Rpresent _ -> true
        | _ -> false)
      fields in
  let all_present = List.length present = List.length fields in
  let tags = if all_present then None else Some (List.map fst present) in
  (fields, tags)

let rec mark_expr cxt ty =
  let px = Btype.proxy ty in
  if not (List.memq px cxt.known_expr) then
    ( cxt.known_expr <- px :: cxt.known_expr;
      mark_desc cxt ty )
  else if not (List.mem_assq px cxt.shared_expr) then
    cxt.shared_expr <-
      (px, (Ident.create "tyrepr_expr", cxt.env)) :: cxt.shared_expr

and mark_desc cxt ty =
  match ty.Types.desc with
  | Ttuple tyl -> List.iter (mark_expr cxt) tyl
  | Tconstr (path, tyl, _) ->
      mark_path cxt path;
      List.iter (mark_expr cxt) tyl
  | Tvariant row ->
      let (fields, _) = get_row_fields row in
      List.iter (mark_row_field cxt) fields
  | Tlink ty | Tsubst ty -> mark_desc cxt ty
  | Tarrow (l, ty1, ty2, _) ->
      mark_expr cxt ty1;
      mark_expr cxt ty2
  | Tpoly (ty, vars) ->
      List.iter (mark_var cxt) vars;
      mark_expr cxt ty
  | Tvar _ | Tunivar _ ->
      raise(TyReprError(Dynamic_type ("free type variable", ty)))
  | Tobject _ | Tpackage _ -> ()
  | Tnil | Tfield _ ->
      fatal_error "Transltyrepr.mark_desc"

and mark_var cxt var =
  let px = Btype.proxy var in
  if not (List.mem_assq px cxt.shared_expr) then begin
    cxt.known_expr <- px :: cxt.known_expr;
    cxt.shared_expr <-
      (px, (Ident.create "tyrepr_var", cxt.env)) :: cxt.shared_expr
  end

and mark_row_field cxt (_, row) =
  match Btype.row_field_repr row with
  | Rpresent None | Reither(true, [], _, _) | Rabsent -> ()
  | Rpresent(Some ty) -> mark_expr cxt ty
  | Reither(c, tyl, _, _) -> List.iter (mark_expr cxt) tyl

and mark_path cxt path =
  if not (List.exists (Path.same path) Predef.builtin_paths) then
    if not (List.exists (fun (p,_) -> Path.same path p) cxt.known_decl) then
      match Env.find_type_dynid path cxt.env with
      | Env.Non_anchored | Env.Dynamic _ -> ()
      | Env.Newtype _ ->
          let decl = Env.find_type path cxt.env in
          may (mark_expr cxt) decl.type_manifest
      | Env.Anchored _ ->
          cxt.known_decl <-
            (path, (Ident.create "tyrepr_decl", cxt.env)) :: cxt.known_decl;
          let decl = Env.find_type path cxt.env in
          List.iter (mark_var cxt) decl.type_params;
          match decl.type_manifest with
          | Some expr -> mark_expr cxt expr
          | None -> mark_kind cxt decl.type_kind

and mark_kind cxt kind =
  match kind with
  | Type_record (fields, _) -> List.iter (mark_field cxt) fields
  | Type_variant constrs -> List.iter (mark_case cxt) constrs
  | Type_abstract -> ()

and mark_case cxt (_,tys,ty) =
  match ty with
  | None ->
      List.iter (mark_expr cxt) tys
  | Some ty ->
      let ty_vars, existentials = gadt_variables ty tys in
      List.iter (mark_var cxt) ty_vars;
      List.iter (mark_var cxt) existentials;
      List.iter (mark_expr cxt) tys;
      mark_expr cxt ty

and mark_field cxt (name,mut,ty) =
  let vars, ty = match (Btype.repr ty).desc with
    | Tpoly (ty, vars) -> vars, ty
    | _ -> [], ty
  in
  List.iter (mark_var cxt) vars;
  mark_expr cxt ty

let build_expr desc =
  (* Build record of type CamlinternalTy.uty *)
  Lprim (Pmakeblock (0, Mutable),
         [ (* expr_id = *)
           new_expr_id;
           (* desc = *)
           desc;
           (* head = *)
           lambda_unit;
         ] )

(** Type expressions and type declarations *)

let rec transl_expr_rec cxt ty =
  let px = Btype.proxy ty in
  try Lvar (fst (List.assq px cxt.shared_expr))
  with Not_found -> transl_expr_rec1 cxt ty

and transl_expr_rec1 cxt ty =
  match ty.Types.desc with
  | Tconstr (path, _, _) ->
      begin match Env.find_type_dynid path cxt.env with
      | Env.Newtype id -> Lvar (Ident.tyrepr id)
      | _ -> build_expr (transl_desc_rec cxt ty)
      end
  | _ -> build_expr (transl_desc_rec cxt ty)

and transl_desc_rec cxt ty =
  match ty.Types.desc with
  | Tconstr(path, [], _) when Path.same path Predef.path_unit ->
      (* CamlinternalTy.DT_unit *)
      Lconst(Const_base (Const_int 0))
  | Tconstr(path, [], _) when Path.same path Predef.path_bool ->
      (* CamlinternalTy.DT_bool *)
      Lconst(Const_base (Const_int 1))
  | Tconstr(path, [], _) when Path.same path Predef.path_int ->
      (* CamlinternalTy.DT_int *)
      Lconst(Const_base (Const_int 2))
  | Tconstr(path, [], _) when Path.same path Predef.path_nativeint ->
      (* CamlinternalTy.DT_nativeint *)
      Lconst(Const_base (Const_int 3))
  | Tconstr(path, [], _) when Path.same path Predef.path_int32 ->
      (* CamlinternalTy.DT_int32 *)
      Lconst(Const_base (Const_int 4))
  | Tconstr(path, [], _) when Path.same path Predef.path_int64 ->
      (* CamlinternalTy.DT_int64 *)
      Lconst(Const_base (Const_int 5))
  | Tconstr(path, [], _) when Path.same path Predef.path_char ->
      (* CamlinternalTy.DT_char *)
      Lconst(Const_base (Const_int 6))
  | Tconstr(path, [], _) when Path.same path Predef.path_string ->
      (* CamlinternalTy.DT_string *)
      Lconst(Const_base (Const_int 7))
  | Tconstr(path, [], _) when Path.same path Predef.path_float ->
      (* CamlinternalTy.DT_float *)
      Lconst(Const_base (Const_int 8))
  | Tconstr(path, [], _) when Path.same path Predef.path_exn ->
      (* CamlinternalTy.DT_exn *)
      Lconst(Const_base (Const_int 9))
  | Tunivar _ ->
      (* CamlinternalTy.DT_univar *)
      Lconst(Const_base (Const_int 10))
  | Tobject _ ->
      (* CamlinternalTy.DT_object *)
      Lconst(Const_base (Const_int 11))
  | Tpackage _ ->
      (* CamlinternalTy.DT_package *)
      Lconst(Const_base (Const_int 12))
  | Tconstr(path, [], _) when Path.same path Predef.path_dummy ->
      (* CamlinternalTy.DT_dummy *)
      Lconst(Const_base (Const_int 13))
  | Tconstr(path, [ty], _) when Path.same path Predef.path_array ->
      (* CamlinternalTy.DT_array of uty *)
      Lprim(Pmakeblock(0, Immutable), [transl_expr_rec cxt ty])
  | Tconstr(path, [ty], _) when Path.same path Predef.path_list ->
      (* CamlinternalTy.DT_list of uty *)
      Lprim(Pmakeblock(1, Immutable), [transl_expr_rec cxt ty])
  | Tconstr(path, [ty], _) when Path.same path Predef.path_option ->
      (* CamlinternalTy.DT_option of uty *)
      Lprim(Pmakeblock(2, Immutable), [transl_expr_rec cxt ty])
  | Tconstr(path, [ty], _) when Path.same path Predef.path_lazy_t ->
      (* CamlinternalTy.DT_lazy of uty *)
      Lprim(Pmakeblock(3, Immutable), [transl_expr_rec cxt ty])
  | Tconstr(path, [ty], _) when Path.same path Predef.path_ty ->
      (* CamlinternalTy.DT_ty of uty *)
      Lprim(Pmakeblock(4, Immutable), [transl_expr_rec cxt ty])
  | Tconstr(path, [ty1;ty2;ty3;ty4;ty5;ty6], _)
      when Path.same path Predef.path_format6 ->
      (* CamlinternalTy.DT_format6 of uty * uty * uty * uty * uty * uty *)
      Lprim(Pmakeblock(5, Immutable),
            [transl_expr_rec cxt ty1; transl_expr_rec cxt ty2;
             transl_expr_rec cxt ty3; transl_expr_rec cxt ty4;
             transl_expr_rec cxt ty5; transl_expr_rec cxt ty6;])
  | Ttuple tyl ->
      (* CamlinternalTy.DT_tuple of uty array *)
      Lprim(Pmakeblock(6, Immutable),
            [make_array (List.map (transl_expr_rec cxt) tyl)])
  | Tarrow (l, ty1, ty2, _) ->
      let ty1 =
        if not (Btype.is_optional l) then ty1
        else match (Ctype.repr ty1).desc with
        | Tconstr (decl, [ty1], _) -> ty1
        | _ -> assert false
      in
      (* CamlinternalTy.DT_arrow of string * uty * uty *)
      Lprim(Pmakeblock(7, Immutable),
            [Lconst (Const_immstring l);
             transl_expr_rec cxt ty1; transl_expr_rec cxt ty2])
  | Tvariant row ->
      let (fields, tags) = get_row_fields row in
      let tags =
        match tags with
        | None -> lambda_unit
        | Some tags ->
            let tags =
              List.map (fun lbl -> Lconst (Const_immstring lbl)) tags in
            Lprim(Pmakeblock (0, Immutable), [make_array tags]) in
      (* CamlinternalTy.DT_pvariant of pvariant_declaration *)
      Lprim(Pmakeblock(8, Immutable),
            [Lprim (Pmakeblock (0, Immutable),
                    [(* pvariant_closed = *)
                     Lconst(Const_base
                              (Const_int (if row.row_closed then 1 else 0)));
                     (* pvariant_constructors = *)
                     make_array (List.map (transl_row_field cxt ty) fields);
                     (* pvariant_tags = *)
                     tags])])
  | Tconstr (path, tyl, _) ->
      (* CamlinternalTy.DT_constr of declaration * uty array *)
      Lprim(Pmakeblock(9, Immutable),
            [transl_path_rec cxt path;
             make_array (List.map (transl_expr_rec cxt) tyl);
             ref_none ])
  | Tvar name ->
      (* CamlinternalTy.DT_var of string option *)
      Lprim(Pmakeblock(10, Immutable),
            [match name with
            | None -> lambda_unit
            | Some name ->
                Lprim(Pmakeblock(0, Immutable), [Lconst(Const_immstring name)])])
  | Tlink ty | Tsubst ty -> transl_desc_rec cxt ty
  | Tnil | Tfield _ | Tpoly _ ->
      fatal_error "Transltyrepr.transl_desc_rec(2)"

and transl_row_field cxt ty (lbl, f) =
  let (ty, opt_amp) =
    match Btype.row_field_repr f with
    | Rpresent None | Reither(true, [], _, _) ->
        (make_array [], false)
    | Rpresent (Some ty) ->
        (make_array [transl_expr_rec cxt ty], false)
    | Reither (opt_amp,tyl,_,_) ->
        (make_array (List.map (transl_expr_rec cxt) tyl), opt_amp)
    | Rabsent ->
        (make_array [], false)
  in
  (* (string * int * bool * uty option) *)
  Lprim(Pmakeblock (0, Immutable),
        [ Lconst(Const_immstring ("`" ^ lbl));
          Lconst(Const_base (Const_int (Btype.hash_variant lbl)));
          Lconst(Const_base (Const_int (if opt_amp then 1 else 0)));
          ty ])

and transl_path_rec cxt path =
  try Lvar (fst (snd (List.find (fun (p,_) -> Path.same path p) cxt.known_decl)))
  with Not_found -> transl_decl_rec cxt path

and transl_decl_rec cxt path =
  let decl = Env.find_type path cxt.env in
  match Env.find_type_dynid path cxt.env with
  | Env.Non_anchored -> raise(TyReprError (Unanchored_type path))
  | Env.Newtype _ -> assert false (* cf. transl_expr_rec or transl_core_expr *)
  | Env.Dynamic path ->
      (* FIXME GRGR functor application ??? *)
      transl_path path
  | Env.Anchored (dynid, _, ext_ids) ->
      let (filename, beg_char, end_char) =
        Location.get_pos_info decl.type_loc.Location.loc_start in
      let kind = Ident.create "kind" in
      (* Build record of type 'CamlinternalTy.declaration' *)
      Llet(Strict, kind, transl_kind_rec cxt decl,
           Lprim (Pmakeblock (0, Immutable),
                  [ (* internal_name = *)
                    transl_dynpath cxt.env dynid;
                    (* external_ids = *)
                    make_array (List.map
                                  (transl_dynpath cxt.env)
                                  (transl_external_ids ext_ids));
                    (* params = *)
                    make_array
                      (List.map (transl_expr_rec cxt) decl.type_params);
                    (* variance = *)
                    transl_variance decl;
                    (* priv = *)
                    transl_private decl;
                    (* body = *)
                    Lvar kind;
                    (* builder = *)
                    transl_builder cxt kind path decl;
                    (* loc = *)
                    Lprim (Pmakeblock (0, Immutable),
                           [Lconst(Const_immstring filename);
                            Lconst(Const_base(Const_int beg_char));
                            Lconst(Const_base(Const_int end_char));])]))

and transl_variance decl =
  make_array
    (List.map2
       (fun ty (co,cn,ct) ->
         if cn && co then
           (* CamlinternalTy.Invariant *)
           Lconst (Const_base (Const_int 0))
         else if not cn then
           (* CamlinternalTy.Covariant *)
           Lconst (Const_base (Const_int 1))
         else
           (* CamlinternalTy.Contravariant *)
           Lconst (Const_base (Const_int 2)))
       decl.type_params decl.type_variance);

and transl_private decl =
  match decl.type_private with
  | Public -> Lconst(Const_base(Const_int 0))
  | Private -> Lconst(Const_base(Const_int 1))

and transl_external_ids ext_ids =
  match ext_ids with
  | None -> []
  | Some (id, env) ->
      match Env.find_type_dynid (Pident id) env with
      | Env.Non_anchored | Env.Newtype _ | Env.Dynamic _ -> assert false
      | Env.Anchored (dynid, _, ext_ids) ->
          let ids = transl_external_ids ext_ids in
          let decl = Env.find_type (Pident id) env in
          if decl.type_manifest = None then dynid :: ids else ids

and transl_variant_case_rec cxt (id, tys, ret_ty) =
  let name = Ident.name id in
  let transl_expr = transl_expr_rec cxt in
  let rty =
    match ret_ty with
    | None -> Lconst(Const_base(Const_int 0))
    | Some { desc = Tconstr (_, params, _) }->
        Lprim(Pmakeblock(0, Immutable),
              [Lprim (Pmakeblock(0, Immutable),
                      [make_array (List.map transl_expr params);
                       Lconst(Const_base(Const_int (0))) ])])
    | Some _ -> assert false
  in
  Lprim(Pmakeblock(0, Immutable),
        [Lconst(Const_immstring name);
         make_array (List.map transl_expr tys);
         rty])

and transl_schema_rec cxt ty =
  let vars, ty = match (Btype.repr ty).desc with
    | Tpoly (ty, vars) -> vars, ty
    | _ -> [], ty
  in
  Lprim(Pmakeblock(0, Immutable),
        [(* vars = *)
         make_array (List.map (transl_expr_rec cxt) vars);
         (* expr = *)
         transl_expr_rec cxt ty])

and transl_field_rec cxt (name,mut,ty) =
  Lprim(Pmakeblock(0, Immutable),
        [Lconst(Const_immstring (Ident.name name));
         ( match mut with
           | Mutable -> Lconst(Const_base(Const_int 0))
           | Immutable -> Lconst(Const_base(Const_int 1)) );
         transl_schema_rec cxt ty])

and transl_kind_rec cxt decl =
  match decl.type_manifest with
  | Some e ->
      (* CamlinternalTy.DT_alias of uty *)
      Lprim (Pmakeblock (0, Immutable), [transl_expr_rec cxt e])
  | None -> transl_kind_rec1 cxt decl.type_kind

and transl_kind_rec1 cxt kind =
  match kind with
  | Type_abstract ->
      (* CamlinternalTy.DT_abstract *)
      Lconst(Const_base(Const_int 0))
  | Type_variant constrs ->
      (* CamlinternalTy.DT_variant of variant_description *)
      Lprim(Pmakeblock(1, Immutable),
            [Lprim(Pmakeblock(0, Immutable),
                   [make_array (List.map (transl_variant_case_rec cxt) constrs)])])
  | Type_record (fields, repr) ->
      (* CamlinternalTy.DT_record of record_description *)
      Lprim(Pmakeblock(2, Immutable),
            [Lprim(Pmakeblock(0, Immutable),
                   [(* record_representation = *)
                    ( match repr with
                    | Record_regular -> Lconst(Const_base(Const_int 0))
                    | Record_float -> Lconst(Const_base(Const_int 1)) );
                    (* record_fields = *)
                    make_array (List.map (transl_field_rec cxt) fields)
                  ])])

and transl_builder cxt kind path decl =
  (* Build a function that instantiate the type declaration. *)
  if decl.type_params = [] then
    (* - without type parameter, do not reallocate. *)
    Lfunction(Curried, [Ident.create ""], Lvar kind)
  else if is_gadt decl.type_kind then
    (* - with gadt, we must filter the returned type in each cases,
         this is actually done in CamlinternalTy.instantiate_decl *)
    Lfunction(Curried, [Ident.create ""], Lvar kind)
  else
    (* Build context for recursive instance compilation:
       - insert type parameter as 'faked shared expr' *)
    let cxt = { cxt with known_expr = []; shared_expr = [] } in
    List.iter (mark_var cxt) decl.type_params;
    let param_ids =
      List.mapi (fun i (_, (id, _)) -> (id, i)) (List.rev cxt.shared_expr) in
    mark_kind cxt decl.type_kind;
    may (mark_expr cxt) decl.type_manifest;
    let kind = transl_kind_rec cxt decl in
    let shared_expr = (* Remove faked type parameter. *)
      remove_first (List.length decl.type_params) (List.rev cxt.shared_expr) in
    let fun_body = (* Build shared type expression. *)
      if shared_expr = [] then kind else
      Lletrec
        (List.map
           (fun (ty,(id, _)) -> (id, transl_expr_rec1 cxt ty))
           shared_expr,
         kind) in
    (* Wrap actual type parameters as function parameters *)
    let params_id = Ident.create "params" in
    Lfunction(Curried, [params_id],
              List.fold_right
                (fun (id, ofs) body ->
                  Llet(Strict, id,
                       Lprim(Parrayrefs Pgenarray,
                             [Lvar params_id;
                              Lconst(Const_base (Const_int ofs))]),
                       body))
                param_ids fun_body)


(** Simplify 'core_type' by replacing prefixed type constructors
    (e.g. '^t') with their external type. Also mark sharings. *)

(* GRGR FIXME name *)
let rec dyn_external env path ofs =
  match Env.find_type_dynid path env with
  | Env.Anchored (_, size, _) when ofs < size -> (env, path)
  | Env.Anchored (_, size, None) -> assert false
  | Env.Anchored (_, size, Some (id, env)) ->
      dyn_external env (Path.Pident id) (ofs - size)
  | _ -> (env, path)

let rec simplify_and_mark_expr cxt cty =
  match cty.ctyp_desc with
  | Ttyp_constr (path, lid, params, ofs) ->
      let decl = Env.find_type path cty.ctyp_env in
      if decl.type_newtype_level <> None then cty else
      let (ext_env, ext_path) = dyn_external cty.ctyp_env path ofs in
      let params' = List.map (simplify_and_mark_expr cxt) params in
      cxt.env <- ext_env;
      if not (List.exists (Path.same ext_path) Predef.builtin_paths) then
        mark_path cxt ext_path;
      { cty with
        ctyp_desc = Ttyp_constr (ext_path, lid, params', 0);
        ctyp_env = ext_env }
  | Ttyp_arrow (lbl, ty1, ty2) ->
      { cty with
        ctyp_desc =
          Ttyp_arrow (lbl, simplify_and_mark_expr cxt ty1,
                      simplify_and_mark_expr cxt ty2) }
  | Ttyp_tuple tyl ->
      { cty with
        ctyp_desc = Ttyp_tuple (List.map (simplify_and_mark_expr cxt) tyl) }
  | Ttyp_alias (ty, var) ->
      let id = Ident.create "tyrepr_alias" in
      let ty' = simplify_and_mark_expr cxt ty in
      let cty = { cty with ctyp_desc = Ttyp_alias (ty', var) } in
      cxt.aliases <- (cty, (id, ty')) :: cxt.aliases;
      cxt.alias_vars <- (var, id) :: cxt.alias_vars;
      cty
  | Ttyp_variant (fields, closed, lbl) ->
      { cty with
        ctyp_desc =
          Ttyp_variant (List.map (simplify_and_mark_row_field cxt) fields,
                        closed, lbl) }
  | Ttyp_poly _ -> assert false
  | Ttyp_any
  | Ttyp_var _ ->
      let ty = Btype.repr cty.ctyp_type in
      if Btype.is_Tvar ty then mark_var cxt ty else mark_expr cxt ty;
      cty
  | Ttyp_package _ | Ttyp_object _ | Ttyp_class _ -> cty (* TODO GRGR *)

and simplify_and_mark_row_field cxt field =
  match field with
  | Ttag (lbl, conj, params) ->
      Ttag (lbl, conj, List.map (simplify_and_mark_expr cxt) params)
  | Tinherit ty -> Tinherit (simplify_and_mark_expr cxt ty)


(** Compilation of 'Typedtree.core_type'. *)

let rec transl_core_type_rec cxt cty =
  try Lvar (fst (List.assq cty cxt.aliases))
  with Not_found -> transl_core_type_rec1 cxt cty

and transl_core_type_rec1 cxt cty =
  match cty.ctyp_desc with
  | Ttyp_alias _ -> assert false
  | Ttyp_any -> transl_expr_rec cxt cty.ctyp_type
  | Ttyp_var var ->
      begin
        try Lvar (List.assoc var cxt.alias_vars)
        with Not_found ->
          if not (Btype.is_Tvar (Btype.repr (cty.ctyp_type))) then
            Location.prerr_warning cxt.loc
              (Warnings.Instantiated_dynamic_var var);
          transl_expr_rec cxt cty.ctyp_type
      end
  | Ttyp_constr (Pident id as path,_,[],_) ->
      begin match Env.find_type_dynid path cxt.env with
      | Env.Newtype id -> Lvar (Ident.tyrepr id)
      | _ -> build_expr (transl_core_desc_rec cxt cty)
      end
  | _ -> build_expr (transl_core_desc_rec cxt cty)

and transl_core_desc_rec cxt cty =
  match cty.ctyp_desc with
  | Ttyp_constr(path, _, [], _) when Path.same path Predef.path_unit ->
      (* CamlinternalTy.DT_unit *)
      Lconst(Const_base (Const_int 0))
  | Ttyp_constr(path, _, [], _) when Path.same path Predef.path_bool ->
      (* CamlinternalTy.DT_bool *)
      Lconst(Const_base (Const_int 1))
  | Ttyp_constr(path, _, [], _) when Path.same path Predef.path_int ->
      (* CamlinternalTy.DT_int *)
      Lconst(Const_base (Const_int 2))
  | Ttyp_constr(path, _, [], _) when Path.same path Predef.path_nativeint ->
      (* CamlinternalTy.DT_nativeint *)
      Lconst(Const_base (Const_int 3))
  | Ttyp_constr(path, _, [], _) when Path.same path Predef.path_int32 ->
      (* CamlinternalTy.DT_int32 *)
      Lconst(Const_base (Const_int 4))
  | Ttyp_constr(path, _, [], _) when Path.same path Predef.path_int64 ->
      (* CamlinternalTy.DT_int64 *)
      Lconst(Const_base (Const_int 5))
  | Ttyp_constr(path, _, [], _) when Path.same path Predef.path_char ->
      (* CamlinternalTy.DT_char *)
      Lconst(Const_base (Const_int 6))
  | Ttyp_constr(path, _, [], _) when Path.same path Predef.path_string ->
      (* CamlinternalTy.DT_string *)
      Lconst(Const_base (Const_int 7))
  | Ttyp_constr(path, _, [], _) when Path.same path Predef.path_float ->
      (* CamlinternalTy.DT_float *)
      Lconst(Const_base (Const_int 8))
  | Ttyp_constr(path, _, [], _) when Path.same path Predef.path_exn ->
      (* CamlinternalTy.DT_exn *)
      Lconst(Const_base (Const_int 9))
  | Ttyp_any ->
      (* CamlinternalTy.DT_univar *)
      Lconst(Const_base (Const_int 10))
  | Ttyp_object _
  | Ttyp_class _ ->
      (* CamlinternalTy.DT_object *)
      Lconst(Const_base (Const_int 11))
  | Ttyp_package _ ->
      (* CamlinternalTy.DT_package *)
      Lconst(Const_base (Const_int 12))
  | Ttyp_constr(path, _, [], _) when Path.same path Predef.path_dummy ->
      (* CamlinternalTy.DT_dummy *)
      Lconst(Const_base (Const_int 13))
  | Ttyp_constr(path, _, [cty], _) when Path.same path Predef.path_array ->
      (* CamlinternalTy.DT_array of uty *)
      Lprim(Pmakeblock(0, Immutable), [transl_core_type_rec cxt cty])
  | Ttyp_constr(path, _, [cty], _) when Path.same path Predef.path_list ->
      (* CamlinternalTy.DT_list of uty *)
      Lprim(Pmakeblock(1, Immutable), [transl_core_type_rec cxt cty])
  | Ttyp_constr(path, _, [cty], _) when Path.same path Predef.path_option ->
      (* CamlinternalTy.DT_option of uty *)
      Lprim(Pmakeblock(2, Immutable), [transl_core_type_rec cxt cty])
  | Ttyp_constr(path, _, [cty], _) when Path.same path Predef.path_lazy_t ->
      (* CamlinternalTy.DT_lazy of uty *)
      Lprim(Pmakeblock(3, Immutable), [transl_core_type_rec cxt cty])
  | Ttyp_constr(path, _, [cty], _) when Path.same path Predef.path_ty ->
      (* CamlinternalTy.DT_ty of uty *)
      Lprim(Pmakeblock(4, Immutable), [transl_core_type_rec cxt cty])
  | Ttyp_constr(path, _, [cty1;cty2;cty3;cty4;cty5;cty6], _)
      when Path.same path Predef.path_format6 ->
      (* CamlinternalTy.DT_format6 of uty * uty * uty * uty * uty * uty *)
      Lprim(Pmakeblock(5, Immutable),
            [transl_core_type_rec cxt cty1; transl_core_type_rec cxt cty2;
             transl_core_type_rec cxt cty3; transl_core_type_rec cxt cty4;
             transl_core_type_rec cxt cty5; transl_core_type_rec cxt cty6;])
  | Ttyp_tuple ctyl ->
      (* CamlinternalTy.DT_tuple of uty array *)
      Lprim(Pmakeblock(6, Immutable),
            [make_array (List.map (transl_core_type_rec cxt) ctyl)])
  | Ttyp_arrow (lbl, cty1, cty2) ->
      let cty1 =
        if not (Btype.is_optional lbl) then cty1
        else match cty1.ctyp_desc with
        | Ttyp_constr (decl, _, [ty1], _) -> ty1
        | _ -> assert false in
      (* CamlinternalTy.DT_arrow of string * uty * uty *)
      Lprim(Pmakeblock(7, Immutable),
            [Lconst (Const_immstring lbl);
             transl_core_type_rec cxt cty1;
             transl_core_type_rec cxt cty2])
  | Ttyp_variant (fields, closed, tags) ->
      (* TODO GRGR warn if not closed and raw variable has been instantiated. *)
      let tags =
        match tags with
        | None -> lambda_unit
        | Some tags ->
            let tags =
              List.map (fun lbl -> Lconst (Const_immstring lbl)) tags in
            Lprim(Pmakeblock (0, Immutable), [make_array tags]) in
      (* CamlinternalTy.DT_pvariant of pvariant_declaration *)
      Lprim(Pmakeblock(8, Immutable),
            [Lprim (Pmakeblock (0, Immutable),
                    [(* pvariant_closed = *)
                     Lconst(Const_base
                              (Const_int (if closed then 1 else 0)));
                     (* pvariant_constructors = *)
                      make_array (transl_core_row_fields cxt cty fields);
                     (* pvariant_tags = *)
                     tags])])
  | Ttyp_constr (path, _, ctyl, _) ->
      cxt.env <- cty.ctyp_env;
      let decl = transl_path_rec cxt path in
      (* CamlinternalTy.DT_constr of declaration * uty array *)
      Lprim(Pmakeblock(9, Immutable),
            [decl;
             make_array (List.map (transl_core_type_rec cxt) ctyl);
             ref_none ])
  | Ttyp_var name ->
      (* CamlinternalTy.DT_var of string option *)
      Lprim(Pmakeblock(10, Immutable),
            (* Some name *)
            [Lprim(Pmakeblock(0, Immutable), [Lconst(Const_immstring name)])])
  | Ttyp_poly _ | Ttyp_alias _ -> assert false

and transl_core_row_fields cxt cty fields =
  List.fold_right (transl_core_row_field cxt cty) fields []

and transl_core_row_field cxt cty field acc =
  match field with
  | Ttag (lbl, opt_amp, params) ->
      (* (string * int * bool * uty array) *)
      Lprim(Pmakeblock (0, Immutable),
            [ Lconst(Const_immstring ("`"^lbl));
              Lconst(Const_base (Const_int (Btype.hash_variant lbl)));
              Lconst
                (Const_base
                   (Const_int (if opt_amp && params <> [] then 1 else 0)));
              make_array (List.map (transl_core_type_rec cxt) params) ]) :: acc
  | Tinherit ty ->
      (* TODO GRGR *)
      raise (TyReprError
               (Dynamic_type ("inherit (not implemented)", cty.ctyp_type)))


(** Main functions. *)

let build_context cxt body =
  if cxt.shared_expr = [] && cxt.known_decl = [] && cxt.aliases = [] then
    body
  else
    Lletrec(List.map
              (fun (_, (id, cty)) ->
                (id, transl_core_type_rec1 cxt cty))
              cxt.aliases
            @ List.map
                (fun (ty,(id, env)) ->
                  cxt.env <- env;
                  (id, transl_expr_rec1 cxt ty))
                cxt.shared_expr
            @ List.map
                (fun (path,(id, env)) ->
                  cxt.env <- env;
                  (id, transl_decl_rec cxt path))
                cxt.known_decl,
            body)

let transl_expr env loc cty ty =
  try
    match cty with
    | None ->
        let ty = Ctype.correct_levels ty in
        let cxt = create_context env loc in
        mark_expr cxt ty;
        let body = transl_expr_rec cxt ty in
        build_context cxt body
    | Some cty ->
        let cxt = create_context env loc in
        let cty = simplify_and_mark_expr cxt cty in
        let body = transl_core_type_rec cxt cty in
        build_context cxt body
  with TyReprError e ->
    raise (Error (loc, ty, e))

let transl_decl env loc path =
  let decl = Env.find_type path env in
  let ty = Ctype.newty (Tconstr (path, decl.type_params, ref Mnil)) in
  try
    let cxt = create_context env loc in
    mark_path cxt path;
    let body = transl_path_rec cxt path in
    build_context cxt body
  with TyReprError e ->
    (* FIXME Custom error *)
    raise (Error (loc, ty, e))

(** Error reporting *)

let report_error ppf ty err =
  Format.fprintf ppf
    "@[Error while building the dynamic representation of the type@ @[%a@]@]@."
    Printtyp.type_expr ty;
  match err with
  | Dynamic_type (msg, ty) ->
      Format.fprintf ppf "@[FIXME error_msg: Dynamic_type %S@ @[%a@]@]@."
        msg
        Printtyp.type_expr ty
  | Unanchored_type p ->
      Format.fprintf ppf "@[FIXME error_msg: Unanchored_type@ @[%a@]@]@."
        Printtyp.path p
