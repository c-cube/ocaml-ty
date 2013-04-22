
module CTy = CamlinternalTy

(** Helpers *)

let may_cons x xs =
  match x with
  | None -> xs
  | Some x -> x :: xs

(** *)

let print_ty ppf ty = CTy.print_uty ppf (CTy.repr ty)
let string_of_ty ty = CTy.string_of_uty (CTy.repr ty)
let print_head_declaration ppf ty =
  match (CTy.repr ty).CTy.desc with
  | CTy.DT_constr (decl, _, _) ->
      CTy.print_declaration ppf decl
  | CTy.DT_var _ -> invalid_arg "Dynamic.print_head_declaration(type variable)"
  | _ -> invalid_arg "Dynamic.print_head_declaration(predefined type)"

(** Type equality *)

type (_, _) eq = Eq: ('a, 'a) eq

let eq (ty1: 'a ty) (ty2: 'b ty): ('a, 'b) eq option =
  if CTy.equal (CTy.repr ty1) (CTy.repr ty2)
  then Some (Obj.magic Eq: ('a, 'b) eq)
  else None
