

open Dynamic

module Printers = Typetable (struct
  type 'a t = Format.formatter -> 'a -> unit
end)

let printers = Printers.create 17
let register_printer ?extern ?intern ty p =
  Printers.add printers  ?extern ?intern ty p
let register_printer1 = Printers.add1 printers
let register_printer2 = Printers.add2 printers

(** Pretty-print values *)

let rec print : type t. t ty -> t Printers.elt =
  fun ty ppf v ->
  try Printers.find printers ty ppf v
  with Not_found ->
    match head ty with
    | Int -> Format.fprintf ppf "%d" v
    | Nativeint -> Format.fprintf ppf "%nd" v
    | Int32 -> Format.fprintf ppf "%ld" v
    | Int64 -> Format.fprintf ppf "%Ld" v
    | Char -> Format.fprintf ppf "%C" v
    | String -> Format.fprintf ppf "%S" v
    | Float -> Format.fprintf ppf "%F" v
    | Exn -> Format.fprintf ppf "Exn: %S" (Printexc.to_string v)
    | Array t -> Format.fprintf ppf "[|%a|]" (print_array t) v
    | Lazy t -> Format.fprintf ppf "%a" (print t) (Lazy.force v)
    | Ty _ -> Format.fprintf ppf "<ty>" (* TODO *)
    | Format6 _ -> Format.fprintf ppf "<format>"
    | Tuple tup -> print_tuple tup ppf v
    | Record r -> print_record r ppf v
    | Sum sum ->
        let (name, DynT (tup, args)) = sum.sum_case v in
        if List.length tup.tuple_fields = 0 then
          Format.fprintf ppf "%s" name
        else
          Format.fprintf ppf "%s %a" name (print_tuple tup) args
    | Arrow _ -> Format.fprintf ppf "<fun>"
    | Opaque -> Format.fprintf ppf "<abstr>"

and print_array : type t. t ty -> Format.formatter -> t array -> unit =
  fun t ppf v ->
  if Array.length v >= 1 then begin
    Format.fprintf ppf "%a" (print t) v.(0);
    for i = 1 to Array.length v - 1 do
      Format.fprintf ppf "; %a" (print t) v.(i);
    done
  end

and print_tuple : type t. t tuple -> Format.formatter -> t -> unit =
  fun tup ppf v ->
    Format.fprintf ppf "(%a)" (print_tuple_fields tup.tuple_fields) v

and print_tuple_fields : type t. t field list -> Format.formatter -> t -> unit =
  fun fields ppf v ->
    match fields with
    | [] -> assert false
    | [Field (ty, { field_get })] ->
        Format.fprintf ppf "%a" (print ty) (field_get v);
    | Field (ty, { field_get }) :: fields ->
        Format.fprintf ppf "%a, %a"
          (print ty) (field_get v)
          (print_tuple_fields fields) v

and print_record : type t . t record -> Format.formatter -> t -> unit =
  fun r ppf v ->
    Format.fprintf ppf "{%a}" (print_record_fields r.record_fields) v

and print_record_fields :
type t. (string * t field) list -> Format.formatter -> t -> unit =
  fun fields ppf v ->
    match fields with
    | [] -> assert false
    | [name, Field (ty, { field_get })] ->
        Format.fprintf ppf "%s = %a" name (print ty) (field_get v);
    | (name, Field (ty, { field_get })) :: fields ->
        Format.fprintf ppf "%s = %a; %a"
          name (print ty) (field_get v)
          (print_record_fields fields) v

let display ?(type t) (v: t) =
  Format.printf "%a\n" (print (type t)) v

(** *)


let _ = display 1
let _ = display 1.3
let _ = display 2l
let _ = display 3L
let _ = display 'e'
let _ = display "Hello"
let _ = display true
let _ = display (Some 4)

let _ = display [|1;2;3|]
let _ = display [|1.;2.;3.|]
let _ = display [1;2;3]
let _ = display [1.;2.;3.]
let _ = display (1,'D',3.4)
let _ = display (ref 3L)

type r = { x: int; y: char; z: float * string }
let _ = display { x = 1; y = 'D'; z = 3.4, "EE" }

type rf = { xf: float; yf: float; zf: float }
let _ = display { xf = 1.; yf = 2.; zf = 3.4 }

type v = A | B | C of int | D of int * int | E of (int * int)
let _ = display A
let _ = display B
let _ = display (C 1)
let _ = display (D (2, 3))
let _ = display (E (2, 3))

type pv = [`A | `B | `C of int | `D of int * int]
let _ = display (`A : pv)
let _ = display (`B : pv)
let _ = display (`C 1 : pv)
let _ = display (`D (2, 3) : pv)

type 'a pv' = ([ `A of 'a * 'list | `B ] as 'list)
let _ = display (`A (3, `A(4, `B)) : int pv')

let rec print_list_content : type t. t ty -> Format.formatter -> t list -> unit =
  fun ty ppf xs ->
  match xs with
  | [] -> ()
  | [x] -> Format.fprintf ppf "%a" (print ty) x
  | x :: xs -> Format.fprintf ppf "%a;%a" (print ty) x (print_list_content ty) xs

let print_list ?(type t) ppf xs =
  match xs with
  | [] -> Format.printf "[]"
  | _ -> Format.printf "[%a]" (print_list_content (type t)) xs

let () =
  register_printer1 (module struct
    type 'a constr = 'a list
    let constr = (type dummy list)
    let action = print_list
   end)

let _ =
  display [1;2;3;4]

module A : sig
  type a
  val a : a
end = struct
  type a = string
  let a = "an opaque value"
end

let _ = display A.a

module B : sig
  type b
  val b : b
end = struct
  type b = B of string
  let b = B "an opaque value"
  let custom_print ppf (B v) = Format.fprintf ppf "custom:B (%s)" v
  let () = register_printer ~extern:true (type b) custom_print
end

let _ = display B.b

module C : sig
  type c
  val c : c
end = struct
  type c = C of string
  let c = C "an opaque value"
  let _ =
    register_printer ~extern:true ~intern:false (type c) (print (type c))
end

let _ = display C.c

module D : sig
  type 'a d
  val d : 'a -> 'a d
end = struct

  type 'a d = D of 'a

  let d x = D x

  let _ =
    register_printer1 ~extern:true ~intern:false
      (module struct
        type 'a constr = 'a d
        let constr = (type dummy d)
        let action ?(type t) ppf v = print (type t d) ppf v
      end)

end

let _ =
  display (D.d ['c']);
  display (D.d (Some 3))
