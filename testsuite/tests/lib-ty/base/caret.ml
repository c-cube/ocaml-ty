
(** '^' syntax. *)

module Ty = CamlinternalTy

let print_name ty =
  match (Ty.expand_head (Ty.repr ty)).Ty.desc with
  | Ty.DT_constr (decl, _, _) ->
      print_endline (Ty.internal_name decl)
  | _ -> assert false

(* Module without coercion *)

let () = print_endline "\nModule\n"

module A = struct

  module A1 = struct

    type a = A
    let () =
      print_name (type a);
      print_name (type ^a);
      print_name (type ^^a)

  end

  let () =
    print_newline ();
    print_name (type A1.a);
    print_name (type ^A1.a)

end

let () =
  print_newline ();
  print_name (type A.A1.a)

(* One coercion *)

let () = print_endline "\n\nOne coercion\n"

module B : sig

  module B1 : sig
    type b
  end

end = struct

  module B1 = struct

    type b = B
    type b1 = B1

    let () =
      print_name (type b);
      print_name (type ^b);
      print_name (type ^^b);
      print_newline();
      print_name (type b1);
      print_name (type ^b1);

  end

    let () =
      print_newline();
      print_name (type B1.b);
      print_name (type ^B1.b);
      print_newline();
      print_name (type B1.b1);

end

let () =
  print_newline ();
  print_name (type B.B1.b)

(* Two coercions *)

 let () = print_endline "\n\nTwo coercions\n"

module C : sig

  module C1 : sig
    type c
  end

end = struct

  module C1 : sig
    type c
    type c1
  end = struct

    type c = C
    type c1 = C1
    type c2 = C2

    let () =
      print_name (type c);
      print_name (type ^c);
      print_name (type ^^c);
      print_newline();
      print_name (type c1);
      print_name (type ^c1);
      print_newline();
      print_name (type c2)

  end

  let () =
    print_newline ();
    print_name (type C1.c);
    print_name (type ^C1.c);
    print_newline ();
    print_name (type C1.c1)

end

let () =
  print_newline ();
  print_name (type C.C1.c)


(* Functor *)

let () = print_endline "\nFunctor\n"

module type S = sig type t end
module M = struct type t = M end

module F(X:S) = struct
  type t = T
  let () =
    print_name (type t);
    print_name (type ^t)
end

module FM = F(M)
let () =
  print_name (type F(M).t)


(* Functor and coercion *)

let () = print_endline "\nFunctor and coercion\n"

module F2(X:S) : sig
  type t
end = struct
  type t = T
  let () =
    print_name (type t);
    print_name (type ^t)
end

module F2M = F2(M)
let () =
  print_name (type F2(M).t)
