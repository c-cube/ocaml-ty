
(** External type identifiers. *)

module Ty = CamlinternalTy

let prefix i =
  if i = 0 then ""
  else String.make i '#' ^ " "

let rec print_ids i decl =
  print_endline (prefix i ^ Ty.internal_name decl);
  match decl.Ty.extern with
  | None -> ()
  | Some decl -> print_ids (i+1) decl

let print_ids ty =
  match (Ty.expand_head (Ty.repr ty)).Ty.desc with
  | Ty.DT_constr (decl, _, _) -> print_ids 0 decl
  | _ -> assert false

(* Without coercion *)

let () = print_endline "\nWithout coercion\n"

module A = struct

  module A1 = struct

    type a = A
    let () =
      print_ids (type a)

  end

  let () =
    print_newline ();
    print_ids (type A1.a)

end


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
      print_ids (type b);
      print_ids (type b1)

  end

end

let () =
  print_newline ();
  print_ids (type B.B1.b)

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
      print_ids (type c);
      print_ids (type c1);
      print_ids (type c2)

  end

  let () =
    print_newline ();
    print_ids (type C1.c);
    print_ids (type C1.c1)

end

let () =
  print_newline ();
  print_ids (type C.C1.c)


(* Functor *)

let () = print_endline "\n\nFunctor\n"

module type S = sig type t end
module M = struct type t = M end
module M2 = struct type t = M2 end

module F(X:S) : sig
  type t
  val t : t ty
end = struct
  type t = T
  let t = (type t)
end
module FM = F(M)
module FM2 = F(M2)

let () =
  print_ids FM.t;
  print_ids (type FM.t);
  print_ids (type F(M).t);
  print_newline ();
  print_ids FM2.t;
  print_ids (type FM2.t);
  print_ids (type F(M2).t);
  print_newline ();
  print_ids FM2.t;
  print_ids (type FM2.t);
  print_ids (type F(M2).t)


(* Generative functor *)

let () = print_endline "\n\nGenerative functor\n"

module Anonymous = F(struct type t = Anonymous end)
module Alias = F(struct type t = int end)
module Coerce = F((M : S))

let () =
  print_ids Anonymous.t; (* FIXME *)
  print_ids (type Anonymous.t);
  print_newline ();
  print_ids Alias.t; (* FIXME *)
  print_ids (type Alias.t);
  print_newline ();
  print_ids Coerce.t; (* FIXME *)
  print_ids (type Coerce.t)


(* Functor coercion *)

let () = print_endline "\n\nFunctor coercion\n"

module D : sig

  module F(X : S) : sig
    type t
    val t : t ty
  end

  module M : sig
    type t
  end

end = struct

  module F(X:S) : sig
    type t
    val t : t ty
  end = struct
    type t = T
    let t = (type t)
  end

  module M = struct
    type t
  end

  module M2 = struct
    type t
  end

  module FM = F(M)
  module FM2 = F(M2)

  let () =
    print_ids FM.t;
    print_ids (type F(M).t);
    print_newline ();
    print_ids FM2.t;
    print_ids (type F(M2).t);
    print_newline ()

end

module DFM = D.F(D.M)

let () =
  print_ids DFM.t;
  print_ids (type D.F(D.M).t)

(* External *)

let () = print_endline "\n\nExternal\n"

let () =
  print_ids Common.t;
  print_ids Common.t';
  print_ids (type Common.t)
