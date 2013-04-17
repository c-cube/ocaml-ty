
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
