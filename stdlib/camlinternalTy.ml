
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
