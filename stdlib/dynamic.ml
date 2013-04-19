
module CTy = CamlinternalTy

(** Type equality *)

type (_, _) eq = Eq: ('a, 'a) eq

let eq (ty1: 'a ty) (ty2: 'b ty): ('a, 'b) eq option =
  if CTy.equal (CTy.repr ty1) (CTy.repr ty2)
  then Some (Obj.magic Eq: ('a, 'b) eq)
  else None
