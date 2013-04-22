
(** *)

val print_ty: Format.formatter -> 'a ty -> unit
val string_of_ty: 'a ty -> string
val print_head_declaration: Format.formatter -> 'a ty -> unit

(** Type equality *)

type (_, _) eq = Eq: ('a, 'a) eq
val eq: 'a ty -> 'b ty -> ('a, 'b) eq option
