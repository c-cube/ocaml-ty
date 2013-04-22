
(** Type equality *)

let () = CamlinternalTy.use_internal_name := true

let test_eq ty1 ty2 =
  match Dynamic.eq ty1 ty2 with
  | Some _ -> ()
  | None ->
      Format.printf "Missing equality: %a = %a@."
        Dynamic.print_ty ty1 Dynamic.print_ty ty2

let test_neq ty1 ty2 =
  match Dynamic.eq ty1 ty2 with
  | None -> ()
  | Some _ ->
      Format.printf "Unexpected equality: %a = %a@."
        Dynamic.print_ty ty1 Dynamic.print_ty ty2

(* Basic type *)

let () =
  test_eq (type unit) (type unit);
  test_eq (type bool) (type bool);
  test_eq (type int) (type int);
  test_eq (type nativeint) (type nativeint);
  test_eq (type int32) (type int32);
  test_eq (type int64) (type int64);
  test_eq (type char) (type char);
  test_eq (type string) (type string);
  test_eq (type float) (type float);
  test_eq (type exn) (type exn);
  test_eq (type unit array) (type unit array);
  test_eq (type bool list) (type bool list);
  test_eq (type int option) (type int option);
  test_eq (type char Lazy.t) (type char Lazy.t);
  test_eq
    (type (unit, unit, int, unit, unit, unit) format6)
    (type (unit, unit, int, unit , unit, unit) format6);
  test_eq (type string ty) (type string ty);
  test_eq (type (unit * bool)) (type (unit * bool));
  test_eq (type (unit * (bool * int) * char)) (type (unit * (bool * int) * char));
  test_eq (type char -> string) (type char -> string);
  test_eq (type c:char -> string) (type c:char -> string);
  test_eq (type ?c:char -> unit -> string) (type ?c:char -> unit -> string);
  test_neq (type char -> string) (type c:char -> string);
  test_neq (type ?c:char -> string) (type c:char -> string);
  (* test_eq *) (* TODO... 'unify' or option to 'allow var renaming' *)
    (* (type ?('abab) -> ?('baba) -> 'abab -> 'baba -> unit) *)
    (* (type ?('abab) -> ?('baba) -> 'abab -> 'baba -> unit); *)
  test_eq (type [ `A | `B ]) (type [ `A | `B ]);
  test_eq (type [< `A | `B ]) (type [< `A | `B ]);
  test_eq (type [> `A | `B ]) (type [> `A | `B ]);
  test_neq (type [< `A | `B ]) (type [> `A | `B ]);
  test_eq (type [< `A | `B > `A ]) (type [< `A | `B > `A ]);
  test_eq (type [ `A of int ]) (type [ `A of int ]);
  test_eq (type [ `A of int * bool ]) (type [ `A of int * bool ]);
  test_neq (type [ `A of int * bool ]) (type [ `A of int * char ])

(* -rectypes *)

let () =
  test_eq (type 'a list as 'a) (type 'a0 list as 'a0);
  test_eq (type 'b list list as 'b) (type 'b0 list list as 'b0);
  test_eq (type ('c * 'c) list as 'c) (type ('c0 * 'c0) list as 'c0);
  test_eq
    (type ((int list as 'd) * 'd * 'd)) (type ((int list as 'd0) * 'd0 * 'd0));
  test_eq (type 'e list as 'e) (type 'e0 list list as 'e0);

(* Alias *)

type a = int list
type b = a option
type 'a c = 'a list

let () =
  test_eq (type int list) (type a);
  test_eq (type int list option) (type b);
  test_eq (type int list) (type int c);
  test_eq (type 'a list as 'a) (type 'b c c c c as 'b)

(* Module without coercion *)

module A = struct

  module A1 = struct

    type a = A
    let a = (type a)
    let a' = (type ^a)
    let a'' = (type ^^a)
    let () =
      test_eq (type a) (type ^a);
      test_eq (type a) (type ^^a)

  end

  let a = (type A1.a)
  let a' = (type ^A1.a)
  let () =
    test_eq (type A1.a) A1.a;
    test_eq (type A1.a) A1.a';
    test_eq (type A1.a) A1.a'';
    test_eq (type A1.a) (type ^A1.a)

end

let () =
  test_eq (type A.A1.a) A.A1.a;
  test_eq (type A.A1.a) A.A1.a';
  test_eq (type A.A1.a) A.A1.a'';
  test_eq (type A.A1.a) A.a;
  test_eq (type A.A1.a) A.a'

(* One coercion *)

module B : sig

  module B1 : sig
    type b
    val b : b ty
    val b' : b ty
    val b'' : b ty
  end
  val b : B1.b ty
  val b' : B1.b ty

end = struct

  module B1 = struct

    type b = B
    let b = (type b)
    let b' = (type ^b)
    let b'' = (type ^^b)
    let () =
      test_eq (type b) (type ^b);
      test_neq (type ^b) (type ^^b);
      test_neq (type b) (type ^^b)

  end

  let b = (type B1.b)
  let b' = (type ^B1.b)
  let () =
    test_eq (type B1.b) B1.b;
    test_eq (type B1.b) B1.b';
    test_neq (type B1.b) B1.b'';
    test_neq (type B1.b) (type ^B1.b)

end

let () =
  test_neq (type B.B1.b) B.B1.b;
  test_neq (type B.B1.b) B.B1.b';
  test_eq (type B.B1.b) B.B1.b'';
  test_neq (type B.B1.b) B.b;
  test_eq (type B.B1.b) B.b'


(* Two coercions *)

module C : sig

  module C1 : sig
    type c
    val c: c ty
    val c': c ty
    val c'': c ty
  end
  val c: C1.c ty
  val c': C1.c ty

end = struct

  module C1 : sig
    type c
    type c1
    val c: c ty
    val c': c ty
    val c'': c ty
    val c1: c1 ty
    val c1': c1 ty
  end = struct

    type c = C
    type c1 = C1
    let c = (type c)
    let c' = (type ^c)
    let c'' = (type ^^c)
    let c1 = (type c1)
    let c1' = (type ^c1)

    let () =
      test_neq (type c) (type ^c);
      test_neq (type ^c) (type ^^c);
      test_neq (type c) (type ^^c);
      test_neq (type c1) (type ^c1)

  end

  let c = (type C1.c)
  let c' = (type ^C1.c)
  let () =
    test_neq (type C1.c) C1.c;
    test_eq (type C1.c) C1.c';
    test_neq (type C1.c) C1.c'';
    test_neq (type C1.c) (type ^C1.c);
    test_neq (type C1.c1) C1.c1;
    test_eq (type C1.c1) C1.c1';

end

let () =
  test_neq (type C.C1.c) C.C1.c;
  test_neq (type C.C1.c) C.C1.c';
  test_eq (type C.C1.c) C.C1.c'';
  test_neq (type C.C1.c) C.c;
  test_eq (type C.C1.c) C.c'

(* Composition of coercion... *)

module E = ((struct
  type t
  let t = (type t)
  let t' = (type ^t)
  let () =
    test_neq (type t) (type ^t)
end : sig
  type t
  val t : t ty
  val t' : t ty
end) : sig
  type t
  val t : t ty
  val t' : t ty
end)

let () =
  test_neq (type E.t) E.t;
  test_eq (type E.t) E.t'


(* Applicative functor *)

module type S = sig type t end
module M = struct type t = M end
module M2 = struct type t = M2 end

module F(X:S) = struct
  type t = T
  let t = (type t)
  let () =
    test_eq (type t) (type ^t)
end

module FM = F(M)
module FM' = F(M)

let () =
  test_eq FM.t FM'.t;
  test_eq (type FM.t) (type FM'.t);
  test_eq (type FM.t) FM.t;
  test_eq (type FM'.t) FM'.t;
  test_eq (type F(M).t) FM.t;
  test_eq (type F(M).t) (type FM.t);
  test_eq (type F(M).t) FM'.t;
  test_eq (type F(M).t) (type FM'.t);
  test_eq (type F(M).t) (type F(M).t);
  test_neq (type F(M).t) (type F(M2).t);
  test_neq (type FM.t) (type F(M2).t)

(* Functor and coercion *)

module F2(X:S) : sig
  type t
  val t : t ty
end = struct
  type t = T
  let t = (type t)
  let () =
    test_neq (type t) (type ^t)
end

module F2M = F2(M)
module F2M' = F2(M)
module F2M2 = F2(M2)

let () =
  test_neq F2M.t F2M'.t; (* ??? GRGR *)
  test_eq (type F2M.t) (type F2M'.t);
  test_neq (type F2M.t) F2M.t;
  test_neq (type F2M'.t) F2M'.t;
  test_neq (type F2(M).t) F2M.t;
  test_eq (type F2(M).t) (type F2M.t);
  test_neq (type F2(M).t) F2M'.t;
  test_eq (type F2(M).t) (type F2M'.t);
  test_eq (type F2(M).t) (type F2(M).t);
  test_neq (type F2(M).t) (type F2(M2).t);
  test_neq (type F2M.t) (type F2(M2).t)

(* ... *)

module Fd(A : sig type t end)(B : sig type t end) = struct
  type t
  let t = (type t)
end

module FdM = Fd(M)
module FdMM2 = Fd(M)(M2)
module FdMM2' = Fd(M)(M2)

let () =
  test_eq FdMM2.t FdMM2'.t;
  test_eq (type FdMM2.t) (type FdMM2'.t);
  test_eq (type FdMM2.t) (type Fd(M)(M2).t);
  test_eq (type FdMM2'.t) (type Fd(M)(M2).t);
  test_eq (type FdMM2.t) (type FdM(M2).t)

(* ... *)

module Fo
    (F : functor (X: S) -> sig type t val t : t ty end)
    (M : sig type t end) = struct
  module A = F(M)
end

module FoFM = Fo(F)(M)
module FoFM' = Fo(F)(M)
module FoFM2 = Fo(F)(M2)
module FoF2M = Fo(F2)(M)

let () =
  test_eq (type FoFM.A.t) (type FoFM'.A.t);
  test_eq FoFM.A.t FoFM'.A.t;
  test_eq (type Fo(F)(M).A.t) (type FoFM.A.t);
  test_neq (type Fo(F2)(M).A.t) (type FoFM.A.t);
  test_neq (type Fo(F2)(M).A.t) (type Fo(F)(M).A.t);
  test_neq (type Fo(F)(M2).A.t) (type FoFM.A.t);
  test_neq (type Fo(F)(M2).A.t) (type Fo(F)(M).A.t)

(* ... *)

let compare (module M : S) (module M2 : S) =
  let module FM = F(M) in
  let module FM2 = F(M2) in
  Dynamic.eq (type FM.t) (type FM2.t) <> None

let () =
  if not (compare (module M) (module M)) then
    Format.printf "Error(1)";
  if compare (module M) (module M2) then
    Format.printf "Error(2)"
