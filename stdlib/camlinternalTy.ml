
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
  desc: description;
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
  | DT_constr of declaration * uty array
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
  extern: declaration option;
  loc: location;
}

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
