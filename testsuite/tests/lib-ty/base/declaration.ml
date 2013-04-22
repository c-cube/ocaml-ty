
(** Type declarations. *)

module Ty = CamlinternalTy

let print ty =
  Format.printf "%a@." Dynamic.print_head_declaration ty

let print_inst ty =
  let (id, params, desc) = Ty.instantiated_description (Ty.repr ty) in
  Format.printf "  @[<2>@[<hv 2>%a => %a@]@."
    Ty.print_uty (Ty.repr ty)
    Ty.print_decl_description (Ty.name_of_path id, desc)

(* Simple type declarations. *)

type a = A1 | A2 of int | A3 of int * bool | A4 of (bool * int)
type b = a list
type c = { c : b }
type d = { mutable d1: int; d2: bool }
type e
type f = private int
type g = private G1 | G2
type h = private [> `A | `B]

let () =
  print (type a);
  print (type b);
  print (type c);
  print (type d);
  print (type e);
  print (type f);
  print (type g);
  print (type h);
  print_newline ()

(* External types *)

let () =
  print (type Common.a);
  print (type Common.b);
  print (type Common.c);
  print (type Common.d);
  print (type Common.e);
  print (type Common.f);
  print (type Common.g);
  print (type Common.h);
  print (type Common.t);
  print Common.t;
  print Common.t';
  print_newline ()


(* Parametrized type declarations ans instance builder. *)

type 'a i = I1 | I2 of 'a * 'a i
type 'a j = 'a list
type 'a k = { k : 'a list }
type 'a l
type 'a m = private 'a list
type 'a n = private N1 | N2 of 'a
type 'a o = private [> `A of 'a ]
type _ p = P1 : int p | P2 : 'a -> 'a p | P3 : 'a * 'b -> ('a * 'b) p
type ('a, 'b) q = Q1 of 'a | Q2 of 'b
type (-'a, +'b) r
type (-_, +_) s = S : ('a -> 'b) -> ('a, 'b) s

let () =
  print (type _ i);
  print_inst (type unit i);
  print (type _ j);
  print_inst (type bool j);
  print (type _ k);
  print_inst (type int k);
  print (type _ l);
  print_inst (type char l);
  print (type _ m);
  print_inst (type string m);
  print (type _ n);
  print_inst (type float n);
  print (type _ o);
  print_inst (type int32 o);
  print (type _ p);
  print_inst (type int p);
  print_inst (type (bool * char) p);
  print_inst (type int64 p);
  print (type (_, _) q);
  print_inst (type (int, float) q);
  print (type (_, _) r);
  print_inst (type (unit, bool) r);
  print (type (_, _) s);
  print_inst (type (char, string) s);
  print_newline ()

(* Constraints *)

type ('a, 'b) t =
    T1 of 'a | T2 of 'b constraint 'a = [> `A ] constraint 'b = [> `B]

let () =
  (* print (type (_,_) t); *) (* FIXME GRGR *)
  print_inst (type ([`A | `C], [< `A | `B | `C > `B]) t)

