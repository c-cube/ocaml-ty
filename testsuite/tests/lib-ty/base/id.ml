
(** Type identifiers. *)

module Ty = CamlinternalTy

let print_name ty =
  match (Ty.expand_head (Ty.repr ty)).Ty.desc with
  | Ty.DT_constr (decl, _, _) ->
      print_endline (Ty.internal_name decl)
  | _ -> assert false


(* Module without coercion *)

let () = print_endline "\nModule\n"

module A = struct

  type a0 = A0
  let () =
    print_name (type a0)

  module A1 = struct

    type a = A
    let () =
      print_name (type a0);
      print_name (type a)

  end

end

let () =
  print_name (type A.a0);
  print_name (type A.A1.a)

(* Module and coercion *)

let () = print_endline "\nCoercion\n"

module B : sig

  type b0
  module B1 : sig type b end

end = struct

  type b0 = B0
  let () =
    print_name (type b0)

  module B1 = struct

    type b = B
    let () =
      print_name (type b0);
      print_name (type b)

  end

end

let () =
  print_name (type B.b0);
  print_name (type B.B1.b)


(* Module aliasing *)

let () = print_endline "\nAlias\n"

module C = struct
  type a = A
  let a = (type a)
end

module C1 = C

module C2 : sig type a val a: a ty end = C

let _ =
  print_name C.a;
  print_name C1.a;
  print_name C2.a;
  print_name (type C.a);
  print_name (type C1.a);
  print_name (type C2.a)


(* Functor *)

let () = print_endline "\nFunctor\n"

module type S = sig type t end
module M = struct type t = M end
module M2 = struct type t = M2 end

module F(X:S) = struct type t = T let t = (type t) end
module FM = F(M)
module FM2 = F(M2)

let () =
  print_name FM.t;
  print_name (type FM.t);
  print_name (type F(M).t);
  print_name FM2.t;
  print_name (type FM2.t);
  print_name (type F(M2).t)


(* Functor and coercion *)

let () = print_endline "\nFunctor and coercion\n"

module F2(X:S) : sig
  type t
  val t : t ty
end = struct
  type t = T
  let t = (type t)
end
module F2M = F2(M)
module F2M2 = F2(M2)

let () =
  print_name F2M.t;
  print_name (type F2M.t);
  print_name (type F2(M).t);
  print_name F2M2.t;
  print_name (type F2M2.t);
  print_name (type F2(M2).t);
  print_name F2M2.t;
  print_name (type F2M2.t);
  print_name (type F2(M2).t)


(* Generative functor *)

let () = print_endline "\nGenerative functor\n"

module Anonymous = F(struct type t = Anonymous end)
module Alias = F(struct type t = int end)
module Coerce = F((M : S))

let () =
  print_name Anonymous.t; (* FIXME ! *)
  print_name (type Anonymous.t);
  print_name Alias.t; (* FIXME ! *)
  print_name (type Alias.t);
  print_name Coerce.t; (* FIXME ! *)
  print_name (type Coerce.t)

(* Generative functor *)

let () = print_endline "\nGenerative functor and coercion\n"

module Anonymous2 = F2(struct type t = Anonymous end)
module Alias2 = F2(struct type t = int end)
module Coerce2 = F2((M : S))

let () =
  print_name Anonymous2.t;
  print_name (type Anonymous2.t);
  print_name Alias2.t;
  print_name (type Alias2.t);
  print_name Coerce2.t;
  print_name (type Coerce2.t)

(* ... *)

module G(X : sig module M : sig type t end end) = struct
  module FM = F(X.M)
  open X
  module FM' = F(M)
end

module GG = G(struct module M = struct type t= GG end end)
