
#include "mlvalues.h"
#include "memory.h"
#include "alloc.h"

/* Primitive for dyntypes. */

CAMLprim value caml_ty_new_expr_id(value unit) {
  static int x = 0;
  return Val_long(++x);
}

CAMLprim value caml_ty_new_coercion_id(value unit) {
  static int x = 0;
  return Val_long(++x);
}

