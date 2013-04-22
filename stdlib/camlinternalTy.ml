
(** Helpers *)

let may f = function None -> () | Some x -> f x
let map_option f o = match o with
  | None -> None
  | Some v -> Some (f v)

(** *)

let implicit_ty_label = "!ty"

(** *)

type path =
  | Pident of int * anchor_kind
  | Pdot of path * string
  | Papply of path * path

and anchor_kind =
  | Anonymous
  | Compunit of string
  | Coercion of path

let rec print_internal_path ppf p =
  match p with
  | Pident (i, Anonymous) ->
      Format.fprintf ppf "anonymous(%d)" i
  | Pident (_, Compunit name) ->
      Format.pp_print_string ppf name
  | Pident (_, Coercion p) ->
      Format.fprintf ppf "[%a]" print_internal_path p
  | Pdot(p, name) ->
      Format.fprintf ppf "%a.%s" print_internal_path p name
  | Papply(p1, p2) ->
      Format.fprintf ppf "%a(%a)" print_internal_path p1 print_internal_path p2

let rec print_path ppf p =
  match p with
  | Pident (i, Anonymous) ->
      Format.fprintf ppf "anonymous(%d)" i
  | Pident (_, Compunit name)
  | Pdot(Pident (_, Anonymous), name) ->
      Format.pp_print_string ppf name
  | Pident (_, Coercion p) ->
      print_path ppf p
  | Pdot(p, name) ->
      Format.fprintf ppf "%a.%s" print_path p name
  | Papply(p1, p2) ->
      Format.fprintf ppf "%a(%a)" print_path p1 print_path p2

let string_of_internal_path p =
  let buf = Buffer.create 50 in
  let ppf = Format.formatter_of_buffer buf in
  print_internal_path ppf p;
  Format.pp_print_flush ppf ();
  Buffer.contents buf

let string_of_path p =
  let buf = Buffer.create 50 in
  let ppf = Format.formatter_of_buffer buf in
  print_path ppf p;
  Format.pp_print_flush ppf ();
  Buffer.contents buf

let name_of_path p =
  match p with
  | Pident (i, Anonymous)
  | Pident (i, Coercion _) -> Format.sprintf "anonymous(%d)" i
  | Pident (_, Compunit name)
  | Pdot(_, name) -> name
  | Papply(_, _) -> assert false

external new_coercion_id: unit -> int = "caml_ty_new_coercion_id"
let toplevel_path = Pident(new_coercion_id(), Compunit "toplevel")
let predef_path = Pident(new_coercion_id(), Compunit "*predef")
let new_predef_path name = Pdot(predef_path, name)

(** *)

type location = string * int * int

type record_representation =
  | Record_regular
  | Record_float

type mutable_flag =
  | Mutable
  | Immutable

type variance =
  | Invariant
  | Covariant
  | Contravariant

type uty = {
  expr_id: int;
  mutable desc: description;
}

and description =
  | DT_unit
  | DT_bool
  | DT_int
  | DT_nativeint
  | DT_int32
  | DT_int64
  | DT_char
  | DT_string
  | DT_float
  | DT_exn
  | DT_array of uty
  | DT_list of uty
  | DT_option of uty
  | DT_lazy of uty
  | DT_ty of uty
  | DT_format6 of uty * uty * uty * uty * uty * uty
  | DT_tuple of uty array
  | DT_arrow of string * uty * uty
  | DT_pvariant of pvariant_description
  | DT_constr of declaration * uty array * decl_description option ref
  | DT_var of string option
  | DT_univar
  | DT_object
  | DT_package
  | DT_dummy

and declaration = {
  decl_id: path;
  params: uty array;
  variance: variance array;
  priv: bool;
  body: decl_description;
  builder: builder;
  extern: declaration option;
  loc: location;
}

and builder = uty array -> decl_description

and declaration_cache = decl_description option ref

and decl_description =
  | DT_alias of uty
  | DT_variant of variant_description
  | DT_record of record_description
  | DT_abstract

and pvariant_description = {
  pvariant_closed: bool;
  pvariant_constructors: (string * int * bool * uty array) array;
  pvariant_required: (string array) option;
}

and variant_description = {
  variant_constant_constructors:
    (string * (uty array * bool) option) array;
  variant_allocated_constructors:
    (string * uty array * (uty array * bool) option) array;
}

and record_description = {
  record_representation : record_representation;
  record_fields : (string * mutable_flag * scheme) array;
}

and scheme = {
  vars: uty array;
  expr: uty;
}

external new_expr_id: unit -> int = "caml_ty_new_expr_id"

let make_expr desc = { expr_id = new_expr_id (); desc; }

let qualified_name decl = string_of_path decl.decl_id
let internal_name decl = string_of_internal_path decl.decl_id
let name decl = name_of_path decl.decl_id

(** *)

external repr: 'a ty -> uty = "%identity"
external ty: uty -> 'a ty = "%identity"

let have_return_types constrs =
  List.exists (fun (_, ret) -> ret <> None)
    (Array.to_list constrs.variant_constant_constructors)
  || List.exists (fun (_, _, ret) -> ret <> None)
       (Array.to_list constrs.variant_allocated_constructors)

let is_gadt decl =
  match decl.body with
  | DT_abstract | DT_record _ | DT_alias _ -> false
  | DT_variant constrs -> have_return_types constrs

let is_var ty =
  match ty.desc with
  | DT_var _ | DT_univar -> true
  | _ -> false


(** Copy/substitute type expression *)

type subst = (uty * uty) list

let rec copy_expr env ty =
  try List.assq ty !env
  with Not_found ->
    let new_ty = make_expr (DT_var None) in (* dummy *)
    env := (ty, new_ty) :: !env;
    new_ty.desc <- copy_desc env ty;
    new_ty
and copy_desc env ty =
  match ty.desc with
  | DT_unit
  | DT_bool
  | DT_int
  | DT_nativeint
  | DT_int32
  | DT_int64
  | DT_char
  | DT_string
  | DT_float
  | DT_exn -> ty.desc

  | DT_array ty -> DT_array (copy_expr env ty)
  | DT_list ty -> DT_list (copy_expr env ty)
  | DT_option ty -> DT_option (copy_expr env ty)
  | DT_lazy ty -> DT_lazy (copy_expr env ty)
  | DT_ty ty -> DT_ty (copy_expr env ty)

  | DT_format6 (ty1, ty2, ty3, ty4, ty5, ty6) ->
      DT_format6 (copy_expr env ty1, copy_expr env ty2,
                  copy_expr env ty3, copy_expr env ty4,
                  copy_expr env ty5, copy_expr env ty6)

  | DT_tuple tyl -> DT_tuple (Array.map (copy_expr env) tyl)
  | DT_arrow (name,ty1,ty2) ->
      DT_arrow (name, copy_expr env ty1, copy_expr env ty2)
  | DT_pvariant pv ->
      DT_pvariant
        { pv with
          pvariant_constructors =
            Array.map (copy_case env) pv.pvariant_constructors; }
  | DT_constr (decl,tyl,_) ->
      DT_constr (decl, Array.map (copy_expr env) tyl, ref None)

  | DT_var _
  | DT_univar
  | DT_object
  | DT_package
  | DT_dummy -> ty.desc

and copy_case env (name, hash, amp, tyo) =
  (name, hash, amp, Array.map (copy_expr env) tyo)

let copy ty = copy_expr (ref []) ty
let substitute subst ty = copy_expr (ref subst) ty


(** Predefined type declaration *)

let predef_decl name params variance builder =
  assert (Array.length params = Array.length variance);
  { decl_id = new_predef_path name;
    params; variance;
    priv = false;
    body = builder params;
    builder;
    extern = None;
    loc = ("*predef",0,0) }

let unit_decl =
  let kind =
    DT_variant
      { variant_constant_constructors =
        [| ("()", None) |];
        variant_allocated_constructors = [| |]; } in
  predef_decl "unit" [||] [||] (fun _ -> kind)

let bool_decl =
  let kind =
    DT_variant
      { variant_constant_constructors =
        [| ("false", None) ; ("true", None) |];
        variant_allocated_constructors = [| |]; } in
  predef_decl "bool" [||] [||] (fun _ -> kind)

let exn_decl =
  let kind =
    DT_variant
      { variant_constant_constructors = [| |];
        variant_allocated_constructors = [| |]; } in
  predef_decl "exn" [||] [||] (fun _ -> kind)

let option_decl =
  predef_decl "option" [| make_expr (DT_var None) |] [| Covariant |]
    (fun params ->
      DT_variant
        { variant_constant_constructors =
            [| ("None", None) |];
          variant_allocated_constructors =
            [| ("Some", [|params.(0)|], None) |]; })

let list_decl =
  let decl_id = new_predef_path "list" in
  let params = [| make_expr (DT_var None) |] in
  let rec decl =
    { decl_id;
      params;
      variance = [| Covariant |];
      priv = false;
      body =
        DT_variant
          { variant_constant_constructors =
              [| ("[]", None) |];
            variant_allocated_constructors =
              [| ("::", [|params.(0); expr|], None) |] } ;
      builder;
      extern = None;
      loc = ("*predef",0,0) }
  and expr =
    { expr_id = new_expr_id ();
      desc = DT_constr (decl, [|params.(0)|], ref None ) }
  and builder params =
    let rec kind =
      DT_variant
        { variant_constant_constructors =
          [| ("[]", None) |];
          variant_allocated_constructors =
          [| ("::", [|params.(0); expr|], None) |]; }
    and expr =
      { expr_id = new_expr_id ();
        desc = DT_constr(decl, params, ref (Some kind)) } in
    kind
  in
  decl

let abstract_decl name params variance =
  predef_decl name params variance (fun _ -> DT_abstract)

let array_decl =
  abstract_decl "array"
    [| make_expr (DT_var None) |] [| Invariant |]

let format6_decl =
  abstract_decl "format6"
    [| make_expr (DT_var None); make_expr (DT_var None);
       make_expr (DT_var None); make_expr (DT_var None);
       make_expr (DT_var None); make_expr (DT_var None); |]
    [| Invariant; Invariant; Invariant; Invariant; Invariant; Invariant; |]

let lazy_decl =
  abstract_decl "lazy_t"
    [| make_expr (DT_var None) |] [| Covariant |]

let ty_decl =
  abstract_decl "ty"
    [| make_expr (DT_var None) |] [| Invariant |]

let int_decl = abstract_decl "int" [||] [||]
let nativeint_decl = abstract_decl "nativeint" [||] [||]
let int32_decl = abstract_decl "int32" [||] [||]
let int64_decl = abstract_decl "int64" [||] [||]
let char_decl = abstract_decl "char" [||] [||]
let string_decl = abstract_decl "string" [||] [||]
let float_decl = abstract_decl "float" [||] [||]

let extract_decl ty =
  match ty.desc with
  | DT_unit -> Some (unit_decl, [||])
  | DT_bool -> Some (bool_decl, [||])
  | DT_int -> Some (int_decl, [||])
  | DT_nativeint -> Some (nativeint_decl, [||])
  | DT_int32 -> Some (int32_decl, [||])
  | DT_int64 -> Some (int64_decl, [||])
  | DT_char -> Some (char_decl, [||])
  | DT_string -> Some (string_decl, [||])
  | DT_float -> Some (float_decl, [||])
  | DT_exn -> Some (exn_decl, [||])
  | DT_array ty -> Some (array_decl, [|ty|])
  | DT_list ty -> Some (list_decl, [|ty|])
  | DT_option ty -> Some (option_decl, [|ty|])
  | DT_lazy ty -> Some (lazy_decl, [|ty|])
  | DT_ty ty -> Some (ty_decl, [|ty|])
  | DT_format6 (ty1, ty2, ty3, ty4, ty5, ty6) ->
      Some (format6_decl, [|ty1;ty2;ty3;ty4;ty5;ty6|])
  | DT_tuple _ | DT_arrow _ | DT_pvariant _ -> None
  | DT_constr (decl, args, _) -> Some (decl, args)
  | DT_var _ | DT_univar | DT_object | DT_package | DT_dummy -> None


(** Instantiation *)

let filter_fwd = ref (fun _ _ _ -> assert false)

let build_gadt_subst ret_params params =
  assert (Array.length params = Array.length ret_params);
  let aux subst t1 t2 =
    match subst with
    | None -> None
    | Some subst -> !filter_fwd subst t1 t2 in
  List.fold_left2 aux (Some [])
    (Array.to_list params) (Array.to_list ret_params)

let instantiate_gadt_constrs constrs params =
  let variant_constant_constructors =
    Array.map
      (function
        | (name, None) -> assert false
        | (name, Some (ret_params, _)) ->
            match build_gadt_subst ret_params params with
            | None ->
                (name, Some (ret_params, true))
            | Some subst ->
                let env = ref subst in
                (name,
                 Some (Array.map (copy_expr env) ret_params, false)))
      constrs.variant_constant_constructors
  in
  let variant_allocated_constructors =
    Array.map
      (function
        | (name, tyl, None) -> assert false
        | (name, tyl, Some (ret_params, _)) ->
            match build_gadt_subst ret_params params with
            | None ->
                (name, tyl, Some (ret_params, true))
            | Some subst ->
                let env = ref subst in
                (name, Array.map (copy_expr env) tyl,
                 Some (Array.map (copy_expr env) ret_params, false)))
    constrs.variant_allocated_constructors
  in
  { variant_constant_constructors; variant_allocated_constructors; }

let instantiated_description ty =
  match ty.desc with
  | DT_constr ({ builder } as decl , params, cache) ->
      begin match !cache with
      | Some instantiated -> (decl.decl_id, params, instantiated)
      | None ->
          let instantiated =
            match decl.body with
            | DT_variant constrs when have_return_types constrs ->
                DT_variant (instantiate_gadt_constrs constrs params)
            | _ -> builder params in
          cache := Some instantiated;
          (decl.decl_id, params, instantiated)
      end
  | _ ->
      match extract_decl ty with
      | Some (decl, params) -> (decl.decl_id, params,decl.builder params)
      | None -> assert false

let expand_head ty =
  match ty.desc with
  | DT_constr ({ body = DT_alias _; priv = false }, _, _) ->
      let (_, _, desc) = instantiated_description ty in
      begin match desc with
      | DT_alias ty -> ty
      | _ -> assert false
      end
  | _ -> ty

(** Equality *)

let rec equal_path p1 p2 =
  match (p1, p2) with
  | (Pident (i1, _), Pident (i2, _)) -> i1 = i2
  | (Pdot (p1, n1), Pdot (p2, n2)) -> n1 = n2 && equal_path p1 p2
  | (Papply (p1, p1'), Papply (p2, p2')) ->
      equal_path p1 p2 && equal_path p1' p2'
  | _ -> false

let rec array_forall2 f a1 a2 i =
  i >= Array.length a1
  || ( f a1.(i) a2.(i)
       && array_forall2 f a1 a2 (succ i) )
let array_forall2 f a1 a2 =
  Array.length a1 == Array.length a2 && array_forall2 f a1 a2 0

let rec equal_expr expr_env ty1 ty2 =
  let ty1 = expand_head ty1 in
  let ty2 = expand_head ty2 in
  ty1.expr_id = ty2.expr_id
  || ( List.exists
         (fun (id1, id2) ->
           (ty1.expr_id = id1 && ty2.expr_id = id2)
           || (ty1.expr_id = id2 && ty2.expr_id = id2))
         !expr_env )
  || ( expr_env := (ty1.expr_id, ty2.expr_id):: !expr_env;
       equal_desc expr_env ty1 ty2 )
and equal_desc expr_env ty1 ty2 =
  match (ty1.desc, ty2.desc) with
  | (DT_unit, DT_unit)
  | (DT_bool, DT_bool)
  | (DT_int, DT_int)
  | (DT_nativeint, DT_nativeint)
  | (DT_int32, DT_int32)
  | (DT_int64, DT_int64)
  | (DT_char, DT_char)
  | (DT_string, DT_string)
  | (DT_float, DT_float)
  | (DT_exn, DT_exn) -> true

  | (DT_array ty1, DT_array ty2)
  | (DT_list ty1, DT_list ty2)
  | (DT_option ty1, DT_option ty2)
  | (DT_lazy ty1, DT_lazy ty2)
  | (DT_ty ty1, DT_ty ty2) -> equal_expr expr_env ty1 ty2

  | (DT_format6 (ty1, ty2, ty3, ty4, ty5, ty6),
     DT_format6 (ty1', ty2', ty3', ty4', ty5', ty6')) ->
       equal_expr expr_env ty1 ty1' &&
       equal_expr expr_env ty2 ty2' &&
       equal_expr expr_env ty3 ty3' &&
       equal_expr expr_env ty4 ty4' &&
       equal_expr expr_env ty5 ty5' &&
       equal_expr expr_env ty6 ty6'

  | (DT_tuple tyl1, DT_tuple tyl2) ->
      Array.length tyl1 = Array.length tyl2
      && array_forall2 (equal_expr expr_env) tyl1 tyl2
  | (DT_arrow (lbl1, ty1, ty1'), DT_arrow (lbl2, ty2, ty2')) ->
      lbl1 = lbl2
      && equal_expr expr_env ty1 ty2
      && equal_expr expr_env ty1' ty2'
  | (DT_pvariant pv1, DT_pvariant pv2) ->
      pv1.pvariant_closed = pv2.pvariant_closed
      && Array.length pv1.pvariant_constructors =
         Array.length pv2.pvariant_constructors
      && array_forall2 (equal_pvariant expr_env)
           pv1.pvariant_constructors pv2.pvariant_constructors
      && pv1.pvariant_required = pv2.pvariant_required
  | (DT_constr (decl1,tyl1, _), DT_constr (decl2,tyl2, _)) ->
      equal_path decl1.decl_id decl2.decl_id
      && array_forall2 (equal_expr expr_env) tyl1 tyl2
  | _ -> false
and equal_pvariant expr_env (name1, _, o1, tyo1) (name2, _, o2, tyo2) =
  if Array.length tyo1 > 1 || Array.length tyo2 > 1 then
    (* FIXME GRGR ??? *)
    invalid_arg "Dynamic.eq: conjunctive type.";
  name1 = name2
  && Array.length tyo1 = Array.length tyo2
  && array_forall2 (equal_expr expr_env) tyo1 tyo2

let equal ty1 ty2 = equal_expr (ref []) ty1 ty2

(** Matching type expression *)

let rec match_expr expr_env subst ty1 ty2 =
  (* ty2 is the pattern. *)
  let ty1 = expand_head ty1 in
  let ty2 = expand_head ty2 in
  ty1.expr_id = ty2.expr_id
  || ( List.exists
         (fun (id1, id2) ->
           (ty1.expr_id = id1 && ty2.expr_id = id2)
           || (ty1.expr_id = id2 && ty2.expr_id = id2))
         !expr_env )
  || ( expr_env := (ty1.expr_id, ty2.expr_id):: !expr_env;
       match_desc expr_env subst ty1 ty2 )
and match_desc expr_env subst ty1 ty2 =
  match (ty1.desc, ty2.desc) with
  | (DT_unit, DT_unit)
  | (DT_bool, DT_bool)
  | (DT_int, DT_int)
  | (DT_nativeint, DT_nativeint)
  | (DT_int32, DT_int32)
  | (DT_int64, DT_int64)
  | (DT_char, DT_char)
  | (DT_string, DT_string)
  | (DT_float, DT_float)
  | (DT_exn, DT_exn) -> true

  | (DT_array ty1, DT_array ty2)
  | (DT_list ty1, DT_list ty2)
  | (DT_option ty1, DT_option ty2)
  | (DT_lazy ty1, DT_lazy ty2)
  | (DT_ty ty1, DT_ty ty2) -> match_expr expr_env subst ty1 ty2

  | (DT_format6 (ty1, ty2, ty3, ty4, ty5, ty6),
     DT_format6 (ty1', ty2', ty3', ty4', ty5', ty6')) ->
       match_expr expr_env subst ty1 ty1' &&
       match_expr expr_env subst ty2 ty2' &&
       match_expr expr_env subst ty3 ty3' &&
       match_expr expr_env subst ty4 ty4' &&
       match_expr expr_env subst ty5 ty5' &&
       match_expr expr_env subst ty6 ty6'

  | (DT_tuple tyl1, DT_tuple tyl2) ->
      Array.length tyl1 = Array.length tyl2
      && array_forall2 (match_expr expr_env subst) tyl1 tyl2
  | (DT_arrow (lbl1, ty1, ty1'), DT_arrow (lbl2, ty2, ty2')) ->
      lbl1 = lbl2
      && match_expr expr_env subst ty1 ty2
      && match_expr expr_env subst ty1' ty2'
  | (DT_pvariant pv1, DT_pvariant pv2) ->
      (* GRGR TODO ??? *)
      invalid_arg "CamlinternalTy.match_expr(pvariant): not implemented"
  | (DT_constr (decl1,tyl1, _), DT_constr (decl2,tyl2, _)) ->
      equal_path decl1.decl_id decl2.decl_id
      && Array.length tyl1 == Array.length tyl2
      && array_forall2 (match_expr expr_env subst) tyl1 tyl2
  | (_, DT_var _) ->
    ( try equal (List.assq ty2 !subst) ty1
      with Not_found -> subst := (ty2, ty1) :: !subst; true )
  | _, _ -> false

let filter subst ty1 ty2 =
  let subst = ref subst in
  if match_expr (ref []) subst ty1 ty2
  then Some !subst
  else None

let () = filter_fwd := filter

let filter ty1 ty2 = filter [] ty1 ty2

(** Pretty-printing *)

open Format

type out_ident = string
let print_ident = pp_print_string

type out_type = (* From outcometree.mli *)
  | Otyp_abstract
  | Otyp_alias of out_type * string
  | Otyp_arrow of string * out_type * out_type
  | Otyp_class of bool * out_ident * out_type list
  | Otyp_constr of out_ident * out_type list
  | Otyp_manifest of out_type * out_type
  | Otyp_object of (string * out_type) list * bool option
  | Otyp_record of (string * bool * out_type) list
  | Otyp_stuff of string
  | Otyp_sum of (string * out_type list * out_type option) list
  | Otyp_tuple of out_type list
  | Otyp_var of string
  | Otyp_variant of
      bool * out_variant * bool * (string list) option
  | Otyp_poly of string list * out_type
  | Otyp_module of string * string list * out_type list

and out_variant =
  | Ovar_fields of (string * bool * out_type list) list
  | Ovar_name of out_ident * out_type list

(* From oprint.ml *)

let rec print_list_init pr sep ppf =
  function
    [] -> ()
  | a :: l -> sep ppf; pr ppf a; print_list_init pr sep ppf l

let rec print_list pr sep ppf =
  function
    [] -> ()
  | [a] -> pr ppf a
  | a :: l -> pr ppf a; sep ppf; print_list pr sep ppf l

let pr_present =
  print_list (fun ppf s -> fprintf ppf "`%s" s) (fun ppf -> fprintf ppf "@ ")

let pr_vars =
  print_list (fun ppf s -> fprintf ppf "'%s" s) (fun ppf -> fprintf ppf "@ ")

let type_parameter ppf (ty, var) =
  fprintf ppf "%s%s"
    (if var = Covariant then "+"
     else if var = Contravariant then "-"
     else "")
    (if ty = "_" then ty else "'"^ty)

let rec print_out_type ppf =
  function
  | Otyp_alias (ty, s) ->
      fprintf ppf "@[%a@ as '%s@]" print_out_type ty s
  | Otyp_poly (sl, ty) ->
      fprintf ppf "@[<hov 2>%a.@ %a@]"
        pr_vars sl
        print_out_type ty
  | ty ->
      print_out_type_1 ppf ty

and print_out_type_1 ppf =
  function
    Otyp_arrow (lab, ty1, ty2) ->
      pp_open_box ppf 0;
      if lab <> "" then
        if lab = implicit_ty_label then
          (pp_print_string ppf "?(")
        else
          (pp_print_string ppf lab; pp_print_char ppf ':');
      print_out_type_2 ppf ty1;
      if lab = implicit_ty_label then (pp_print_string ppf ")");
      pp_print_string ppf " ->";
      pp_print_space ppf ();
      print_out_type_1 ppf ty2;
      pp_close_box ppf ()
  | ty -> print_out_type_2 ppf ty
and print_out_type_2 ppf =
  function
    Otyp_tuple tyl ->
      fprintf ppf "@[<0>%a@]" (print_typlist print_simple_out_type " *") tyl
  | ty -> print_simple_out_type ppf ty
and print_simple_out_type ppf =
  function
    Otyp_class (ng, id, tyl) ->
      fprintf ppf "@[%a%s#%a@]" print_typargs tyl (if ng then "_" else "")
        print_ident id
  | Otyp_constr (id, tyl) ->
      pp_open_box ppf 0;
      print_typargs ppf tyl;
      print_ident ppf id;
      pp_close_box ppf ()
  | Otyp_object (fields, rest) ->
      fprintf ppf "@[<2>< %a >@]" (print_fields rest) fields
  | Otyp_stuff s -> pp_print_string ppf s
  | Otyp_var s -> fprintf ppf "'%s" s
  | Otyp_variant (non_gen, row_fields, closed, tags) ->
      let print_present ppf =
        function
          None | Some [] -> ()
        | Some l -> fprintf ppf "@;<1 -2>> @[<hov>%a@]" pr_present l
      in
      let print_fields ppf =
        function
          Ovar_fields fields ->
            print_list print_row_field (fun ppf -> fprintf ppf "@;<1 -2>| ")
              ppf fields
        | Ovar_name (id, tyl) ->
            fprintf ppf "@[%a%a@]" print_typargs tyl print_ident id
      in
      fprintf ppf "%s[%s@[<hv>@[<hv>%a@]%a ]@]" (if non_gen then "_" else "")
        (if closed then if tags = None then " " else "< "
         else if tags = None then "> " else "? ")
        print_fields row_fields
        print_present tags
  | Otyp_alias _ | Otyp_poly _ | Otyp_arrow _ | Otyp_tuple _ as ty ->
      pp_open_box ppf 1;
      pp_print_char ppf '(';
      print_out_type ppf ty;
      pp_print_char ppf ')';
      pp_close_box ppf ()
  | Otyp_abstract | Otyp_manifest _-> ()
  | Otyp_record lbls ->
      fprintf ppf "{%a@;<1 -2>}"
        (print_list_init print_out_label (fun ppf -> fprintf ppf "@ ")) lbls
  | Otyp_sum constrs ->
      fprintf ppf "@;<0 2>%a"
        (print_list print_out_constr (fun ppf -> fprintf ppf "@ | ")) constrs
  | Otyp_module (p, n, tyl) ->
      fprintf ppf "@[<1>(module %s" p;
      let first = ref true in
      List.iter2
        (fun s t ->
          let sep = if !first then (first := false; "with") else "and" in
          fprintf ppf " %s type %s = %a" sep s print_out_type t
        )
        n tyl;
      fprintf ppf ")@]"
and print_fields rest ppf =
  function
    [] ->
      begin match rest with
        Some non_gen -> fprintf ppf "%s.." (if non_gen then "_" else "")
      | None -> ()
      end
  | [s, t] ->
      fprintf ppf "%s : %a" s print_out_type t;
      begin match rest with
        Some _ -> fprintf ppf ";@ "
      | None -> ()
      end;
      print_fields rest ppf []
  | (s, t) :: l ->
      fprintf ppf "%s : %a;@ %a" s print_out_type t (print_fields rest) l
and print_row_field ppf (l, opt_amp, tyl) =
  let pr_of ppf =
    if opt_amp then fprintf ppf " of@ &@ "
    else if tyl <> [] then fprintf ppf " of@ "
    else fprintf ppf ""
  in
  fprintf ppf "@[<hv 2>`%s%t%a@]" l pr_of (print_typlist print_out_type " &")
    tyl
and print_typlist print_elem sep ppf =
  function
    [] -> ()
  | [ty] -> print_elem ppf ty
  | ty :: tyl ->
      print_elem ppf ty;
      pp_print_string ppf sep;
      pp_print_space ppf ();
      print_typlist print_elem sep ppf tyl
and print_typargs ppf =
  function
    [] -> ()
  | [ty1] -> print_simple_out_type ppf ty1; pp_print_space ppf ()
  | tyl ->
      pp_open_box ppf 1;
      pp_print_char ppf '(';
      print_typlist print_out_type "," ppf tyl;
      pp_print_char ppf ')';
      pp_close_box ppf ();
      pp_print_space ppf ()

and print_out_type_decl ppf (name, args, ty, priv, constraints) =
  let print_constraints ppf params =
    List.iter
      (fun (ty1, ty2) ->
         fprintf ppf "@ @[<2>constraint %a =@ %a@]" print_out_type ty1
           print_out_type ty2)
      params
  in
  let type_defined ppf =
    match args with
      [] -> pp_print_string ppf name
    | [arg] -> fprintf ppf "@[%a@ %s@]" type_parameter arg name
    | _ ->
        fprintf ppf "@[(@[%a)@]@ %s@]"
          (print_list type_parameter (fun ppf -> fprintf ppf ",@ ")) args name
  in
  let print_name_args ppf = fprintf ppf "type %t" type_defined in
  let print_private ppf = function
    true -> fprintf ppf " private"
  | false -> () in
  let print_out_tkind ppf = function
  | Otyp_abstract -> ()
  | Otyp_record lbls ->
      fprintf ppf " =%a {%a@;<1 -2>}"
        print_private priv
        (print_list_init print_out_label (fun ppf -> fprintf ppf "@ ")) lbls
  | Otyp_sum constrs ->
      fprintf ppf " =%a@;<1 2>%a"
        print_private priv
        (print_list print_out_constr (fun ppf -> fprintf ppf "@ | ")) constrs
  | ty ->
      fprintf ppf " =%a@;<1 2>%a"
        print_private priv
        print_out_type ty
  in
  fprintf ppf "@[<2>@[<hv 2>%t%a@]%a@]"
    print_name_args
    print_out_tkind ty
    print_constraints constraints
and print_out_constr ppf (name, tyl,ret_type_opt) =
  match ret_type_opt with
  | None ->
      begin match tyl with
      | [] ->
          pp_print_string ppf name
      | _ ->
          fprintf ppf "@[<2>%s of@ %a@]" name
            (print_typlist print_simple_out_type " *") tyl
      end
  | Some ret_type ->
      begin match tyl with
      | [] ->
          fprintf ppf "@[<2>%s :@ %a@]" name print_simple_out_type  ret_type
      | _ ->
          fprintf ppf "@[<2>%s :@ %a -> %a@]" name
            (print_typlist print_simple_out_type " *")
            tyl print_simple_out_type ret_type
      end


and print_out_label ppf (name, mut, arg) =
  fprintf ppf "@[<2>%s%s :@ %a@];" (if mut then "mutable " else "") name
    print_out_type arg

(* *)

let use_internal_name = ref false

type printing_context = {
    mutable visited_objects: uty list;
    mutable aliased: uty list;
    mutable delayed: uty list;
    mutable names: (uty * string) list;
    mutable named_vars: string list;
    mutable name_counter: int;
  }

let create_printing_context () = {
  visited_objects = []; aliased = []; delayed = [];
  names = []; named_vars = []; name_counter = 0;
}

let rec new_name cxt =
  let name =
    if cxt.name_counter < 26
    then String.make 1 (Char.chr(97 + cxt.name_counter))
    else String.make 1 (Char.chr(97 + cxt.name_counter mod 26)) ^
           string_of_int(cxt.name_counter / 26) in
  cxt.name_counter <- cxt.name_counter + 1;
  if List.mem name cxt.named_vars
  || List.exists (fun (_, name') -> name = name') cxt.names
  then new_name cxt
  else name

let name_of_type cxt t =
  try List.assq t cxt.names
  with Not_found ->
    match t.desc with
    | DT_var (Some name) ->
        let current_name = ref name in
        let i = ref 0 in
        while List.exists (fun (_, name') -> !current_name = name') cxt.names do
          current_name := name ^ (string_of_int !i);
          i := !i + 1;
        done;
        !current_name
    | _ ->
        let name = new_name cxt in
        cxt.names <- (t, name) :: cxt.names;
        name

let check_name_of_type cxt ty = ignore(name_of_type cxt ty)

let remove_names cxt tyl =
  let tyl = Array.to_list tyl in
  cxt.names <- List.filter (fun (ty,_) -> not (List.memq ty tyl)) cxt.names

let aliasable ty =
  match ty.desc with
  | DT_var _ -> false
  | _ -> true

let is_aliased cxt ty = List.memq ty cxt.aliased
let add_alias cxt ty =
  if not (is_aliased cxt ty) then begin
    cxt.aliased <- ty :: cxt.aliased
  end

let add_delayed cxt t =
  if not (List.memq t cxt.delayed) then cxt.delayed <- t :: cxt.delayed

let rec mark_loops_rec cxt visited ty =
  if List.memq ty visited && aliasable ty then add_alias cxt ty else
  let visited = ty :: visited in
  match ty.desc with
  | DT_unit | DT_bool | DT_int | DT_nativeint | DT_int32 | DT_int64
  | DT_char | DT_string | DT_float | DT_exn ->
      ()
  | DT_array ty | DT_list ty | DT_option ty | DT_lazy ty | DT_ty ty ->
      mark_loops_rec cxt visited ty
  | DT_format6 (ty1, ty2, ty3, ty4, ty5, ty6) ->
      mark_loops_rec cxt visited ty1;
      mark_loops_rec cxt visited ty2;
      mark_loops_rec cxt visited ty3;
      mark_loops_rec cxt visited ty4;
      mark_loops_rec cxt visited ty5;
      mark_loops_rec cxt visited ty6
  | DT_tuple tys ->
      Array.iter (mark_loops_rec cxt visited) tys
  | DT_arrow(_, ty1, ty2) ->
      mark_loops_rec cxt visited ty1; mark_loops_rec cxt visited ty2
  | DT_pvariant pv ->
      Array.iter (mark_loops_case cxt visited) pv.pvariant_constructors
  | DT_constr (path, tys, _) ->
      Array.iter (mark_loops_rec cxt visited) tys
  | DT_var _ | DT_univar | DT_object | DT_package | DT_dummy ->
      ()

and mark_loops_case cxt visited (_, _, _, oty) =
  Array.iter (mark_loops_rec cxt visited) oty

and mark_loops_scheme cxt visited sty =
  Array.iter (fun t -> add_alias cxt t) sty.vars;
  mark_loops_rec cxt visited sty.expr

let mark_loops_desc cxt desc =
  match desc with
  | DT_abstract -> ()
  | DT_alias ty -> mark_loops_rec cxt [] ty
  | DT_variant cstrs ->
      Array.iter
        (fun (_, ret_type_opt) ->
          may (fun (tys, _) -> Array.iter (mark_loops_rec cxt []) tys)
            ret_type_opt)
        cstrs.variant_constant_constructors;
      Array.iter
        (fun (_, args, ret_type_opt) ->
          may (fun (tys, _) -> Array.iter (mark_loops_rec cxt []) tys)
            ret_type_opt;
          Array.iter (mark_loops_rec cxt []) args)
        cstrs.variant_allocated_constructors
  | DT_record r ->
      Array.iter
        (fun (_, _, sty) -> mark_loops_scheme cxt [] sty)
        r.record_fields


let mark_loops ty =
  let cxt = create_printing_context () in
  mark_loops_rec cxt [] ty;
  cxt

let is_optional l = l <> "" && l.[0] = '?'
let is_implicit_ty l = l = implicit_ty_label

let rec tree_of_typexp cxt ty =
  if List.mem_assq ty cxt.names && not (List.memq ty cxt.delayed) then
    Otyp_var (name_of_type cxt ty)
  else
    let pr_typ () =
      match ty.desc with
      | DT_unit -> Otyp_constr ("unit", [])
      | DT_bool -> Otyp_constr ("bool", [])
      | DT_int -> Otyp_constr ("int", [])
      | DT_nativeint -> Otyp_constr ("nativeint", [])
      | DT_int32 -> Otyp_constr ("Int32.t", [])
      | DT_int64 -> Otyp_constr ("Int64.t", [])
      | DT_char -> Otyp_constr ("char", [])
      | DT_string -> Otyp_constr ("string", [])
      | DT_float -> Otyp_constr ("float", [])
      | DT_exn -> Otyp_constr ("exn", [])
      | DT_array ty -> Otyp_constr ("array", [tree_of_typexp cxt ty])
      | DT_list ty -> Otyp_constr ("list", [tree_of_typexp cxt ty])
      | DT_option ty -> Otyp_constr ("option", [tree_of_typexp cxt ty])
      | DT_lazy ty -> Otyp_constr ("lazy_t", [tree_of_typexp cxt ty])
      | DT_ty ty -> Otyp_constr ("ty", [tree_of_typexp cxt ty])
      | DT_format6 (ty1, ty2, ty3, ty4, ty5, ty6) ->
          Otyp_constr ("ty", [tree_of_typexp cxt ty1; tree_of_typexp cxt ty2;
                              tree_of_typexp cxt ty3; tree_of_typexp cxt ty4;
                              tree_of_typexp cxt ty5; tree_of_typexp cxt ty6])
      | DT_tuple tyl ->
          Otyp_tuple (tree_of_typlist cxt tyl)
      | DT_arrow(l, ty1, ty2) ->
          Otyp_arrow (l, tree_of_typexp cxt ty1, tree_of_typexp cxt ty2)
      | DT_pvariant pv ->
          let fields =
            Array.to_list
              (Array.map
                 (fun (lbl,_,opt, tyl) ->
                   (lbl, opt,
                    Array.to_list (Array.map (tree_of_typexp cxt) tyl)))
                 pv.pvariant_constructors) in
          Otyp_variant
            (false, Ovar_fields fields, pv.pvariant_closed,
             map_option Array.to_list pv.pvariant_required)
      | DT_constr(decl, tyl, _) ->
          let name =
            if !use_internal_name then
              string_of_internal_path decl.decl_id
            else
              string_of_path decl.decl_id in
          Otyp_constr (name, tree_of_typlist cxt tyl)
      | DT_var _ | DT_univar ->
          Otyp_var (name_of_type cxt ty)
      | DT_object ->
          Otyp_abstract (* FIXME GRGR *)
      | DT_package ->
          Otyp_abstract (* FIXME GRGR *)
      | DT_dummy ->
          Otyp_constr ("dummy", [])
  in
  if List.memq ty cxt.delayed then
    cxt.delayed <- List.filter ((!=) ty) cxt.delayed;
  if is_aliased cxt ty && aliasable ty then begin
    check_name_of_type cxt ty;
    Otyp_alias (pr_typ (), name_of_type cxt ty) end
  else pr_typ ()

and tree_of_typlist cxt tyl =
  Array.to_list (Array.map (tree_of_typexp cxt) tyl)

let tree_of_constraints cxt params =
  Array.fold_right
    (fun ty list ->
       let ty' =
         match ty.desc with
         | DT_var _ -> ty
         | _ -> make_expr ty.desc in
       if ty != ty' then
         let tr = tree_of_typexp cxt ty in
         (tr, tree_of_typexp cxt ty') :: list
       else list)
    params []

let tree_of_scheme cxt sty =
  if sty.vars = [||] then tree_of_typexp cxt sty.expr else
  let old_delayed = cxt.delayed in
  (* Make the names delayed, so that the real type is
     printed once when used as proxy *)
  Array.iter (add_delayed cxt) sty.vars;
  let tl = Array.to_list (Array.map (name_of_type cxt) sty.vars) in
  let tr = Otyp_poly (tl, tree_of_typexp cxt sty.expr) in
  (* Forget names when we leave scope *)
  remove_names cxt sty.vars;
  cxt.delayed <- old_delayed; tr

let rec tree_of_type_decl decl =

  let name = name_of_path decl.decl_id in
  let cxt = create_printing_context () in
  Array.iter (add_alias cxt) decl.params;
  Array.iter (mark_loops_rec cxt []) decl.params;
  Array.iter (check_name_of_type cxt) decl.params;
  mark_loops_desc cxt decl.body;
  let type_param = function Otyp_var id -> id | _ -> "?" in
  let abstr = decl.priv || decl.body = DT_abstract || is_gadt decl in
  let args =
    Array.to_list
      (Array.mapi
         (fun i ty ->
           (type_param (tree_of_typexp cxt ty),
            if abstr || not (is_var ty)
            then decl.variance.(i)
            else Invariant ))
         decl.params) in
  let constraints = tree_of_constraints cxt decl.params in
  let body = tree_of_desc cxt name decl.body in
  (name, args, body, decl.priv, constraints)

and tree_of_desc cxt name desc =
  match desc with
  | DT_abstract -> Otyp_abstract
  | DT_alias ty -> tree_of_typexp cxt ty
  | DT_variant cstrs -> Otyp_sum (tree_of_constructors cxt name cstrs)
  | DT_record r -> Otyp_record (tree_of_record cxt r)

and tree_of_constructors cxt dname cstrs =
  List.fold_right
    (fun (name, ret) acc ->
      match ret with
      | None -> (name, [], None) :: acc
      | Some (_, true) -> acc (* Impossible GADT case *)
      | Some (ret_type, false) ->
          let nm = cxt.names in
          cxt.names <- [];
          let ret = Otyp_constr (dname, tree_of_typlist cxt ret_type) in
          cxt.names <- nm;
          (name, [], Some ret) :: acc)
    (Array.to_list cstrs.variant_constant_constructors)
    (List.fold_right
       (fun (name, args, ret) acc ->
         match ret with
         | None ->
             (name, tree_of_typlist cxt args, None) :: acc
         | Some (ret_type, true) -> acc (* Impossible GADT case *)
         | Some (ret_type, false) ->
             let nm = cxt.names in
             cxt.names <- [];
             let ret = Otyp_constr (dname, tree_of_typlist cxt ret_type) in
             let args = tree_of_typlist cxt args in
             cxt.names <- nm;
             (name, args, Some ret) :: acc)
       (Array.to_list cstrs.variant_allocated_constructors)
       [])

and tree_of_record cxt r =
  Array.to_list
    (Array.map
       (fun (name, mut, sty) -> (name, mut = Mutable, tree_of_scheme cxt sty))
       r.record_fields)

let print_uty ppf ty =
  let cxt = mark_loops ty in
  print_out_type ppf (tree_of_typexp cxt ty)

let string_of_uty uty =
  let buf = Buffer.create 50 in
  let ppf = Format.formatter_of_buffer buf in
  print_uty ppf uty;
  Format.pp_print_flush ppf ();
  Buffer.contents buf

let print_declaration ppf decl =
  print_out_type_decl ppf (tree_of_type_decl decl)

let print_decl_description ppf (name, desc) =
  let cxt = create_printing_context () in
  mark_loops_desc cxt desc;
  print_out_type ppf (tree_of_desc cxt name desc)
