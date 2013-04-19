
(** Type equality *)

type (_, _) eq = Eq: ('a, 'a) eq
val eq: 'a ty -> 'b ty -> ('a, 'b) eq option
