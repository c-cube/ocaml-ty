
(** Type introspection. *)

open Dynamic

(* Not so much typed external representation for value *)
type variant =
  | VInt of int
  | VNativeint of nativeint
  | VInt32 of int32
  | VInt64 of int64
  | VChar of char
  | VString of string
  | VFloat of float
  | VExn of exn
  | VTy of CamlinternalTy.uty
  | VArray of variant list
  | VLazy of variant Lazy.t
  | VTuple of variant list
  | VVariant of string * variant list
  | VRecord of (string * variant) list

exception VariantMismatch

let rec variantize : type t. t ty -> t -> variant =
  fun (type t) (t: t ty) (v: t) ->
  match head t with
  | Int -> VInt v
  | Nativeint -> VNativeint v
  | Int32 -> VInt32 v
  | Int64 -> VInt64 v
  | Char -> VChar v
  | String -> VString v
  | Float -> VFloat v
  | Exn -> VExn v
  | Ty t -> VTy (CamlinternalTy.repr v)
  | Format6 _ -> failwith "Not implemented"
  | Arrow _ -> failwith "Not implemented"
  | Opaque -> invalid_arg "variantize"
  | Array t ->
      VArray (Array.to_list (Array.map (fun v -> variantize t v) v))
  | Lazy t ->
      VLazy (lazy (variantize t (Lazy.force v)))
  | Tuple tup ->
      VTuple
        (List.map
           (fun (Field (ty, {field_get})) -> variantize ty (field_get v))
           tup.tuple_fields)
  | Record r ->
      VRecord
        (List.map
           (fun (name, Field (ty, { field_get })) ->
             (name, variantize ty (field_get v)))
           r.record_fields)
  | Sum sum ->
      let (name, DynT(tup, args)) = sum.sum_case v in
      VVariant
        (name,
         (List.map
            (fun (Field (ty, { field_get })) -> variantize ty (field_get args))
            tup.tuple_fields))

let rec devariantize : type t. t ty -> variant -> t =
  fun (type t) (t: t ty) (v: variant) ->
  ((match (head t, v) with
  | Int, VInt i -> i
  | Nativeint, VNativeint i -> i
  | Int32, VInt32 i -> i
  | Int64, VInt64 i -> i
  | Char, VChar c -> c
  | String, VString s -> s
  | Float, VFloat f -> f
  | Exn, VExn e -> e
  | Ty t, VTy t' ->
      if not (CamlinternalTy.equal (CamlinternalTy.repr t) t') then
        raise VariantMismatch;
      CamlinternalTy.ty t'
  | Array t, VArray [] -> [| |]
  | Array t, VArray vl ->
      let args = Array.of_list vl in
      let arr = Array.create (Array.length args) (devariantize t args.(0)) in
      for i = 1 to Array.length args - 1 do
        arr.(i) <- devariantize t args.(i)
      done;
      arr
  | Lazy t, VLazy v -> lazy (devariantize t (Lazy.force v))
  | Tuple tup, VTuple vl -> devariantize_tuple tup vl
  | Record r, VRecord vl -> devariantize_record r vl
  | Sum sum, VVariant (name, vl) -> devariantize_case sum name vl
  | _ -> raise VariantMismatch) : t)

and devariantize_tuple : type t. t tuple -> variant list -> t =
  fun tup vl ->
  let field_builder ?(type t) _ i =
    try devariantize (type t) (List.nth vl i)
    with Failure _ -> raise VariantMismatch (* Incorrect arity *) in
  tuple_builder tup { field_builder }

and devariantize_record : type t. t record -> (string * variant) list -> t =
  fun r vl ->
  let field_builder ?(type t) name _ =
    try devariantize (type t) (List.assoc name vl)
    with Not_found -> raise VariantMismatch (* Missing field *) in
  record_builder r { field_builder }

and devariantize_case : type t. t sum -> string -> variant list -> t =
  fun sum name vl ->
    try
      match List.assoc name sum.sum_cases with
      | SumCase_constant sel ->
          if vl <> [] then raise VariantMismatch; (* Incorrect arity *)
          case_builder sel ()
      | SumCase_allocated (sel, tup) ->
          case_builder sel (devariantize_tuple tup vl)
    with Not_found -> raise VariantMismatch (* Unknown constructor *)

let test_eq ?(type t) (x: t) =
  let x' = devariantize (type t) (variantize (type t) x) in
  if x = x' then
    Format.printf "OK@."
  else
    Format.printf "Incorrect for type %a@." Dynamic.print_ty (type t)

let test_exn ?(type t) (x: t) t2 =
  try
    ignore (devariantize t2 (variantize (type t) x));
    Format.printf "Should have failed@."
  with exn ->
    Format.printf "Exn: %s@." (Printexc.to_string exn)

let test_exn' v t =
  try
    ignore (devariantize t v);
    Format.printf "Should have failed@."
  with exn ->
    Format.printf "Exn: %s@." (Printexc.to_string exn)

(* Basic types *)

let () =
  test_eq ();
  test_eq true;
  test_eq 3;
  test_eq 3n;
  test_eq 3l;
  test_eq 3L;
  test_eq 'c';
  test_eq "CCC";
  test_eq 3.0;
  test_eq Not_found;
  test_eq [|();();()|];
  test_eq [true;true;false];
  test_eq (Some 3);
  test_eq (type string);
  test_eq ((), true);
  test_eq ((), (false, 3), 'c')

let () =
  test_exn (type string) (type char ty);
  test_exn (3, true) (type (int * bool * char));
  test_exn () (type bool)

(* Sum type and records *)

type a = A1 | A2 | A3 of int | A4 of (int * char) | A5 of char * int
type b = Nil | Cons of int * b
type c = { c1: int; c2: int * char; }

let () =
  test_eq A1;
  test_eq A2;
  test_eq (A3 3);
  test_eq (A4 (3,'d'));
  test_eq (A5 ('c',4));
  test_eq Nil;
  test_eq (Cons (3, Nil));
  test_eq (Cons (1, Cons(2, Cons (3, Nil))));
  test_eq { c1 = 3; c2 = (2, 'a') }

let () =
  test_exn A1 (type b);
  test_exn (Cons (3, Nil)) (type a);
  test_exn' (VVariant ("A3", [])) (type a);
  test_exn' (VVariant ("A1", [VInt 1])) (type a);
  test_exn' (VRecord [("c2", VTuple [VInt 3; VChar 'c'])]) (type c);
  test_exn' (VRecord [("c1", VInt 3)]) (type c);
  test_exn' (VRecord [("d1", VInt 3)]) (type c);

(* Parameterised sum and record. *)

type ('a, 'b) d = D1 | D2 | D3 of 'a | D4 of ('a * 'b) | D5 of 'b * 'a
type 'a e = Nil' | Cons' of 'a * 'a e
type ('a, 'b) f = { f1: 'a; f2: 'a * 'b }
type 'a g = G1 of 'a | G2 of ('a * 'a) g

let () =
  test_eq (D1 : (int, char) d);
  test_eq (D2 : (int, char) d);
  test_eq (D3 3 : (int, char) d);
  test_eq (D4 (3,'d') : (int, char) d);
  test_eq (D5 ('c',4) : (int, char) d);
  test_eq (Nil' : int e);
  test_eq (Cons' (3, Nil') : int e);
  test_eq (Cons' (1, Cons' (2, Cons' (3, Nil'))) : int e);
  test_eq { c1 = 3; c2 = (2, 'a') };
  test_eq (G1 3);
  test_eq (G2 (G1 (3,4)));
  test_eq (G2 (G2 (G1 ((1,2),(3,4)))))

(* Polymorphic variant *)

type h = [ `H1 | `H2 | `H3 of int | `H4 of int * char ]

let () =
  test_eq (`H1 : h);
  test_eq (`H2 : h);
  test_eq (`H3 3 : h);
  test_eq (`H4 (3, 'c') : h)

(* GADT *)

type _ i =
  | I1 : int i
  | I2 : bool i
  | I3 : 'a -> 'a i
  | I4 : 'b -> 'a i
  | I5 : 'a i * 'a i -> 'a i
  | I6 : 'a i * 'b i -> ('a * 'b) i
  | I7 : ('a * 'a) i -> 'a i

let () =
  test_eq (I1);
  test_eq (I2);
  test_eq (I3 false);
  test_eq (I3 'c');
  test_eq (I5 (I1, I3 3));
  test_eq (I6 (I1, I2));
  test_eq (I7 (I6 (I2, I3 true)))

let () =
  test_exn I1 (type bool i);
  test_exn I2 (type int i);
  test_exn (I3 true) (type int i);
  test_exn ((I4 'c') : int i) (type int i);
  test_exn (I5 (I2, I2)) (type int i);
  test_exn (I6 (I1, I2)) (type int i);
  test_exn (I6 (I1, I2)) (type (bool * int) i);
  test_exn (I7 (I6 (I2, I2))) (type int i)


let read ?(type t) vl = devariantize (type t) vl

let g () =
  let x = read (VInt 4) in
  Format.printf "%d\n" (x + 3)

let h ?(type t) () =
  let y = devariantize (type t) (VInt 4) in
  let x : t = read (VInt 4) in
  (y, x)
