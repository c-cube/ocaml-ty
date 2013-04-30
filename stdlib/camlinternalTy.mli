
val implicit_ty_label: string

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

type record_representation = private
  | Record_regular
  | Record_float

type mutable_flag = private
  | Mutable
  | Immutable

type variance =
  | Invariant
  | Covariant
  | Contravariant

type location = private  string * int * int

type builder
type declaration_cache
type dynamic_head
type head_cache

type uty = private {
  expr_id: int;
  mutable desc: description;
  mutable head: head_cache;
}

and description = private
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
  | DT_constr of declaration * uty array * declaration_cache
  | DT_var of string option
  | DT_univar
  | DT_object
  | DT_package
  | DT_dummy

and declaration = private {
  decl_id: path;
  params: uty array;
  variance: variance array;
  priv: bool;
  body: decl_description;
  builder: builder;
  extern: declaration option;
  loc: location;
}

and decl_description = private
  | DT_alias of uty
  | DT_variant of variant_description
  | DT_record of record_description
  | DT_abstract

and pvariant_description = private {
  pvariant_closed: bool;
  pvariant_constructors: (string * int * bool * uty array) array;
  pvariant_required: (string array) option;
}

and variant_description = private {
  variant_constant_constructors:
    (string * (uty array * bool) option) array;
  variant_allocated_constructors:
    (string * uty array * (uty array * bool) option) array;
}

and record_description = private {
  record_representation : record_representation;
  record_fields : (string * mutable_flag * scheme) array;
}

and scheme = private {
  vars: uty array;
  expr: uty;
}

val repr: 'a ty -> uty
val ty: uty -> 'a ty

val expand_head: uty -> uty
val instantiated_description: uty -> path * uty array * decl_description
val extract_decl: uty -> (declaration * uty array) option
val build_dynamic_head: (uty -> dynamic_head) -> uty -> dynamic_head

val equal: uty -> uty -> bool
val equal_path: path -> path -> bool

val copy: uty -> uty

type subst = (uty * uty) list
val substitute: subst -> uty -> uty
val filter: uty -> uty -> subst option

val name: declaration -> string
val qualified_name: declaration -> string
val internal_name: declaration -> string

val use_internal_name: bool ref
val print_uty: Format.formatter -> uty -> unit
val string_of_uty: uty -> string
val print_declaration: Format.formatter -> declaration -> unit
val print_decl_description:
    Format.formatter -> (string * decl_description) -> unit
