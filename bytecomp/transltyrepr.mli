
open Typedtree
open Lambda


val dynpath_new_compunit_id: string -> lambda
val dynpath_new_anonymous_id: lambda
val dynpath_new_coercion_id: Env.t -> Path.t option -> lambda
val dynpath_apply: lambda -> lambda -> lambda
val transl_dynpath: Env.t -> Path.t -> lambda
val transl_module_dynpath: module_expr -> lambda

val transl_dynpath_init: Ident.t list -> lambda
val transl_dynpath_init_pack: string -> string list -> lambda

val transl_expr:
    Env.t -> Location.t ->
    Typedtree.core_type option -> Types.type_expr -> lambda

type error
exception Error of Location.t * Types.type_expr * error
val report_error: Format.formatter -> Types.type_expr -> error -> unit
