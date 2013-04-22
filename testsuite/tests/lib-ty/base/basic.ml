
(** Basic types: runtime representation and pretty-printing. *)

module Ty = CamlinternalTy

let print ty =
  let ty = Ty.expand_head (Ty.repr ty) in
  Format.printf "%a@." Ty.print_uty ty

let typeof ?(type t) (_ : t) = (type t)

(** Explicit type expressions. *)

let () =
  print (type unit);
  print (type bool);
  print (type int);
  print (type nativeint);
  print (type int32);
  print (type int64);
  print (type char);
  print (type string);
  print (type float);
  print (type exn);
  print (type unit array);
  print (type bool list);
  print (type int option);
  print (type char Lazy.t);
  print (type (unit, unit, int, unit, unit, unit) format6);
  print (type string ty);
  print (type (unit * bool));
  print (type (unit * (bool * int) * char));
  print (type char -> string);
  print (type c:char -> string);
  print (type ?c:char -> unit -> string);
  print (type ?('abab) -> ?('baba) -> 'abab -> 'baba -> unit);
  print (type [ `A | `B ]);
  print (type [< `A | `B ]);
  print (type [> `A | `B ]);
  print (type [< `A | `B > `A ]);
  print (type [ `A of int ]);
  print (type [ `A of int * bool ]);
  print (type [< `A of int & bool ])

let () =
  print (type 'a list as 'a);
  print (type 'b list list as 'b);
  print (type ('c * 'c) list as 'c);
  print (type ((int list as 'd) * 'd * 'd))

(** Implicit type expression. *)

let () =
  print (typeof ());
  print (typeof true);
  print (typeof 3);
  print (typeof 3n);
  print (typeof 3l);
  print (typeof 3L);
  print (typeof 'x');
  print (typeof "");
  print (typeof 0.);
  print (typeof Not_found);
  print (typeof [|()|]);
  print (typeof [true]);
  print (typeof (Some 3));
  print (typeof (lazy 'c'));
  print (typeof ("" : (unit,unit,int,unit,unit,unit) format6));
  print (typeof (type string));
  print (typeof ((), true));
  print (typeof ((), (false,2), 'c'));
  print (typeof (fun c -> String.make 3 c));
  print (typeof (fun ~c -> String.make 3 c));
  print (typeof (fun ?(c = 'a') () -> String.make 3 c));
  print (typeof `A);
  print (typeof (`A : [ `A | `B ]));
  print (typeof (`A : [< `A | `B ]));
  print (typeof (`A 3));
  print (typeof (`A (2, true)));
  print (typeof (`A : [< `A | `B of int & bool]))

let rec x = [x]

let () =
  print (typeof x)
