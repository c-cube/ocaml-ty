
open Lambda

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

(** FIXME GRGR *)

let transl_dynpath_init ids =
  make_sequence (fun id ->
    Lambda.Lprim(Lambda.Psetglobal (Ident.dynpath id), [lambda_unit]))
    ids

let transl_dynpath_init_pack targetname names =
  make_sequence (fun name ->
    let fullname = targetname ^ "." ^ name in
    let modid = Ident.create_persistent fullname in
    Lambda.Lprim(Lambda.Psetglobal (Ident.dynpath modid), [lambda_unit]))
    names
