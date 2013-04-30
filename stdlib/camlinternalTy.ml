
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

external new_expr_id: unit -> int = "caml_ty_new_expr_id"
