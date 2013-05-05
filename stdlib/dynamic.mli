
(** *)

val print_ty: Format.formatter -> 'a ty -> unit
val string_of_ty: 'a ty -> string
val print_head_declaration: Format.formatter -> 'a ty -> unit

(** Type equality *)

type (_, _) eq = Eq: ('a, 'a) eq
val eq: 'a ty -> 'b ty -> ('a, 'b) eq option

(** Type introspection *)

type _ head = private
  | Int: int head
  | Nativeint: nativeint head
  | Int32: int32 head
  | Int64: int64 head
  | Char: char head
  | String: string head
  | Float: float head
  | Exn: exn head
  | Array: 'a ty -> 'a array head
  | Lazy: 'a ty ->  'a lazy_t head
  | Ty: 'a ty -> 'a ty head
  | Format6: ('a ty * 'b ty * 'c ty * 'd ty * 'e ty * 'f ty) ->
      ( ('a,'b,'c,'d,'e,'f) format6 ) head
  | Tuple: 'a tuple -> 'a head
  | Record: 'a record -> 'a head
  | Sum: 'a sum -> 'a head
  | Arrow: 'a ty * 'b ty -> ('a -> 'b) head
  | Opaque: 'a head

and 'a tuple = private {
  tuple_fields: 'a field list
}

and 'a record = private {
  record_fields: (string * 'a field) list;
}

and _ field = private
  | Field: 'b ty * ('a, 'b) field_accessors -> 'a field

and ('a, 'b) field_accessors = private {
  field_get: 'a -> 'b;
  field_set: ('a -> 'b -> unit) option;
}

and dyn_tuple = DynT: 'a tuple * 'a -> dyn_tuple

and 'a sum = private {
  sum_case: 'a -> string * dyn_tuple;
  sum_cases: (string * 'a sum_case) list;
}

and _ sum_case = private
 | SumCase_constant: ('a, unit) case_selector -> 'a sum_case
 | SumCase_allocated: ('a, 'b) case_selector * 'b tuple -> 'a sum_case

and (_,_) case_selector

type field_builder = { field_builder: 'a. ?('a) -> string -> int -> 'a }
val tuple_builder: 'a tuple -> field_builder -> 'a
val record_builder: 'a record -> field_builder -> 'a
val case_builder: ('a, 'b) case_selector -> 'b -> 'a

val head: 'a ty -> 'a head

(** Association table *)

module type Typetable = sig

  type t
  type 'a elt

  val create: int -> t

  val add: t -> ?extern:bool -> ?intern:bool -> 'a ty -> 'a elt -> unit

  module type Constr1 = sig
    type 'a constr
    val constr: dummy constr ty
      (* [constr] could be removed if we introduce <transparent> signatures *)
    val action : ?('a) -> 'a constr elt
  end
  val add1: t -> ?extern:bool -> ?intern:bool -> (module Constr1) -> unit

  module type Constr2 = sig
    type ('a, 'b) constr
    val constr: (dummy, dummy) constr ty
      (* [constr] could be removed if we introduce <transparent> signatures *)
    val action : ?('a) -> ?('b) -> ('a, 'b) constr elt
  end
  val add2: t -> ?extern:bool -> ?intern:bool -> (module Constr2) -> unit

  (* ... *)

  val find: t -> 'a ty -> 'a elt

end

module Typetable(T : sig type 'a t end) : Typetable with type 'a elt = 'a T.t

(** *)

module Constr1(T : sig type <transparent> 'a constr end) : sig
  type _ is_instance = Eq : 'a ty -> 'a T.constr is_instance
  val is_constr : 'a ty -> 'a is_instance option
  (* val create : 'a ty -> 'a constr ty *)
  (* val decompose : 'a constr ty -> 'a ty *)
end
