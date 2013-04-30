
type path = private
  | Pident of int * anchor_kind
  | Pdot of path * string
  | Papply of path * path

and anchor_kind = private
  | Anonymous
  | Compunit of string
  | Coercion of path

val print_path: Format.formatter -> path -> unit
val print_internal_path: Format.formatter -> path -> unit

val string_of_path: path -> string
val string_of_internal_path: path -> string
val name_of_path: path -> string
val toplevel_path: path
