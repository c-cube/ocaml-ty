
module CTy = CamlinternalTy

(** Helpers *)

let map_option f = function
  | None -> None
  | Some v -> Some (f v)

let may_cons x xs =
  match x with
  | None -> xs
  | Some x -> x :: xs

let rec array_forall f a i =
  i >= Array.length a
  || ( f a.(i)
       && array_forall f a (succ i) )
let array_forall f a = array_forall f a 0

let rec array_forall2 f a1 a2 i =
  i >= Array.length a1
  || ( f a1.(i) a2.(i)
       && array_forall2 f a1 a2 (succ i) )
let array_forall2 f a1 a2 =
  Array.length a1 == Array.length a2 && array_forall2 f a1 a2 0

let rec array_find f a i =
  if i >= Array.length a then raise Not_found;
  if f a.(i) then a.(i) else array_find f a (succ i)
let array_find f a = array_find f a 0


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

let eq ?strict (ty1: 'a ty) (ty2: 'b ty): ('a, 'b) eq option =
  if CTy.equal ?strict (CTy.repr ty1) (CTy.repr ty2)
  then Some (Obj.magic Eq: ('a, 'b) eq)
  else None

(** Nominal type instrospectin *)

module Constr1(T : sig type <transparent> 'a constr end) : sig
  type _ is_instance = Eq : 'a ty -> 'a T.constr is_instance
  val is_constr : 'a ty -> 'a is_instance option
  (* val create : 'a ty -> 'a T.constr ty *)
  val decompose : 'a T.constr ty -> 'a ty
end = struct
  let internal_name =
    (CTy.extract_resolved_decl (CTy.repr (type 'a T.constr))).CTy.internal_name
  type _ is_instance = Eq : 'a ty -> 'a T.constr is_instance
  let is_constr (type t) (t: t ty) : t is_instance option  =
    match CTy.extract_decl (CTy.expand_head (CTy.repr t)) with
    | Some (decl, params)
      when CTy.equal_path ~strict:false decl.CTy.internal_name internal_name ->
        Some (Obj.magic (Eq (CTy.ty params.(0))))
    | _ -> None
  let decompose (ty: 'a T.constr ty) =
    match CTy.extract_decl (CTy.expand_head (CTy.repr ty)) with
    | Some (decl, params)
      when CTy.equal_path ~strict:false decl.CTy.internal_name internal_name ->
        CTy.ty params.(0)
    | _ -> assert false

end

module Predef = struct

  module List = Constr1(struct type 'a constr = 'a list end)

  module Tuple2 = struct

    type _ is_instance = Eq : 'a ty * 'b ty -> ('a * 'b) is_instance
    let is_constr (type t) (t: t ty) : t is_instance option  =
      match (CTy.expand_head (CTy.repr t)).CTy.desc with
      | CTy.DT_tuple [| ty1; ty2 |] ->
          Some (Obj.magic (Eq (CTy.ty ty1, CTy.ty ty2)))
      | _ -> None

    let decompose (t: ('a * 'b) ty) : 'a ty * 'b ty =
      match (CTy.expand_head (CTy.repr t)).CTy.desc with
      | CTy.DT_tuple [| ty1; ty2 |] -> (CTy.ty ty1, CTy.ty ty2)
      | _ -> assert false

  end

end

(** Structural type introspection *)

type record_representation = CamlinternalTy.record_representation =
  | Record_regular
  | Record_float

type ('a, 'b) field_accessors =
  int * CamlinternalTy.mutable_flag * CamlinternalTy.record_representation

type _ field = Field: 'b ty * ('a, 'b) field_accessors -> 'a field
type 'a tuple = {
  tuple_fields: 'a field list;
}
and 'a record = {
  record_fields: (string * 'a field) list;
  record_repr: record_representation;
}

let tuple_head tys : 'a tuple =
  { tuple_fields =
      Array.to_list
        (Array.mapi
           (fun i field_ty ->
             Field (CTy.ty field_ty,
                    (i, CTy.Immutable, CTy.Record_regular))) tys) }

let record_head record : 'a record =
  { record_fields =
      Array.to_list
        (Array.mapi
           (fun i (field_name, mutable_flag, scheme) ->
             (* scheme.CTy.vars are left as is. If passed to the 'head'
                function, they will be described as 'Opaque'. *)
             let field_ty = CTy.ty scheme.CTy.expr in
             (field_name,
              Field (field_ty,
                     (i, mutable_flag, record.CTy.record_representation ))))
           record.CTy.record_fields);
    record_repr = record.CTy.record_representation }

let field_get (pos, mut, double) obj =
  match double with
  | CTy.Record_float ->
      Obj.magic (Obj.double_field (Obj.repr obj) pos)
  | CTy.Record_regular ->
      Obj.obj (Obj.field (Obj.repr obj) pos)

let field_mutable (pos, mut, double) = mut = CTy.Mutable

let field_set ((pos, mut, double) : ('a, 'b) field_accessors) (obj: 'a) (v: 'b) =
  match mut with
  | CTy.Immutable -> invalid_arg "Dynamic.field_set"
  | CTy.Mutable ->
      match double with
      | CTy.Record_float ->
          Obj.set_double_field (Obj.repr obj) pos (Obj.magic v)
      | CTy.Record_regular ->
          Obj.set_field (Obj.repr obj) pos (Obj.repr v)

type field_builder = { field_builder: 'a. ?('a) -> string -> int -> 'a }

let tuple_builder (tup : 'a tuple) builder =
  let obj = Obj.new_block 0 (List.length tup.tuple_fields) in
  List.iteri
    (fun i (Field (ty, _)) ->
      (* FIXME avoid Obj.magic *)
      let v =
        (Obj.magic builder.field_builder : _ -> string -> int -> _)
          ty "" i in
      Obj.set_field obj i (Obj.repr v))
    tup.tuple_fields;
  Obj.obj obj

let is_float uty = match uty.CTy.desc with CTy.DT_float -> true | _ -> false

let record_builder (r : 'a record) builder =
  match r.record_repr with
  | CTy.Record_float ->
      let obj = Array.create (List.length r.record_fields) 0. in
      List.iteri
        (fun i (name, Field (ty, _)) ->
          assert(is_float (CTy.repr ty));
          let v =
            (Obj.magic builder.field_builder : _ -> string -> int -> float)
              ty name i in
          obj.(i) <- v)
        r.record_fields;
      Obj.magic obj
  | CTy.Record_regular ->
      let obj = Obj.new_block 0 (List.length r.record_fields) in
      List.iteri
        (fun i (name, Field (ty, _)) ->
          (* FIXME avoid Obj.magic *)
          let v =
            (Obj.magic builder.field_builder : _ -> string -> int -> _)
              ty name i in
          Obj.set_field obj i (Obj.repr v))
        r.record_fields;
      Obj.obj obj

(** *)

type (_,_) case_selector =
  | CaseSel_constant of int
  | CaseSel_allocated_sum of int * bool
  | CaseSel_allocated_pvariant of int * bool

type _ sum_case =
 | SumCase_constant: ('a, unit) case_selector -> 'a sum_case
 | SumCase_allocated: ('a, 'b) case_selector * 'b tuple -> 'a sum_case


type sum_desc =
  | Pvariant of (string * int * bool * CTy.uty array) array
  | Variant of string option array * (string * CTy.uty array) option array

type 'a sum = {
  sum_desc: sum_desc;
  sum_cases: (string * 'a sum_case) list;
}

let sum_description sum = sum.sum_cases

let is_impossible_case return_type =
  match return_type with
  | None -> false
  | Some (ret_params, impossible) -> impossible

type case_argument = CaseArg: 'a ty * 'a -> case_argument

let build_args tys obj =
  Array.to_list
    (Array.mapi
       (fun i ty -> CaseArg (Obj.magic ty, Obj.obj (Obj.field obj i)))
       tys)

let sum_get sum v =
  let v = Obj.repr v in
  match sum.sum_desc with
  | Variant (constant, allocated) ->
      if Obj.is_block v then begin
        match allocated.(Obj.tag v) with
        | None ->
            (* FIXME GRGR use opaque or 'lazy failure' *)
            invalid_arg "Dynamic.sum_case";
        | Some (name, [| { CTy.desc = CTy.DT_tuple tys } |] ) ->
            (name, build_args tys (Obj.field v 0))
        | Some (name, tys) -> (name, build_args tys v)
      end else begin
        match constant.(Obj.obj v) with
        | None ->
            (* FIXME GRGR use opaque or 'lazy failure' *)
            invalid_arg "Dynamic.sum_case";
        | Some name -> (name, [])
      end
  | Pvariant pvs ->
      if Obj.is_block v then begin
        let hash : int = Obj.obj (Obj.field v 0) in
        let (name, _, _, ty) =
          array_find (fun (_,hash',_,_) -> hash = hash') pvs in
        let args =
          match ty with
          | [| { CTy.desc = CTy.DT_tuple tys } |] ->
              build_args tys (Obj.field v 1)
          | [| ty |]->
              [CaseArg (Obj.magic ty, Obj.obj (Obj.field v 1))]
          | [||] -> assert false
          | _ -> invalid_arg "Dynamic.head: conjunction in polymorphic variant" in
        (name, args)
      end else begin
        let hash : int = Obj.obj v in
        let (name, _, _, _) = array_find (fun (_,hash',_,_) -> hash = hash') pvs in
        (name, [])
      end

let case_builder sel arg =
  match sel with
  | CaseSel_constant tag -> Obj.magic tag
  | CaseSel_allocated_sum (tag, wrap) ->
      if wrap then
        let obj = Obj.new_block tag 1 in
        Obj.set_field obj 0 (Obj.repr arg);
        Obj.obj obj
      else
        let obj = Obj.dup (Obj.repr arg) in
        Obj.set_tag obj tag;
        Obj.obj obj
  | CaseSel_allocated_pvariant (hash, unwrap) ->
      let obj = Obj.new_block 0 2 in
      Obj.set_field obj 0 (Obj.repr hash);
      let arg =
        if unwrap
        then (Obj.field (Obj.repr arg) 0)
        else Obj.repr arg
      in
      Obj.set_field obj 1 arg;
      Obj.obj obj

(** *)

let sum_head (desc: CTy.variant_description) =
  let constant, allocated =
    List.fold_right
      (fun (name, tys, ret_ty) (consts, allocs) ->
        if Array.length tys = 0 then
          let case = if is_impossible_case ret_ty then None else Some name in
          (case :: consts, allocs)
        else
          let case =
            (* FIXME GRGR use opaque or 'lazy failure' *)
            if is_impossible_case ret_ty then None else Some (name, tys) in
          (consts, (case :: allocs)) )
      (Array.to_list desc.CTy.variant_constructors)
      ([], []) in
  let (_,_,sum_cases) =
    Array.fold_left
      (fun (i,j,cases) (name, tys, ret_ty) ->
          if Array.length tys = 0 then
            let cases =
              if is_impossible_case ret_ty then cases else
              (name, SumCase_constant (CaseSel_constant i)) :: cases in
            (i+1,j,cases)
          else
            let cases =
              if is_impossible_case ret_ty then cases else
              let (selector, tys) =
                match tys with
                | [| { CTy.desc = CTy.DT_tuple tys } |] ->
                    (CaseSel_allocated_sum (j, true), tys)
                | _ ->
                    (CaseSel_allocated_sum (j, false), tys) in
              (name, SumCase_allocated (selector, tuple_head tys)) :: cases in
            (i,j+1,cases))
      (0,0,[]) desc.CTy.variant_constructors
  in
  { sum_desc = Variant (Array.of_list constant, Array.of_list allocated);
    sum_cases; }

(** *)

let pvariant_head pvs =
  let sum_cases =
    List.map
      (fun (name, hash, lbl, tyl) ->
        match tyl with
        | [||] -> (name, SumCase_constant (CaseSel_constant hash))
        | [| { CTy.desc = CTy.DT_tuple tys } |] ->
            let selector = CaseSel_allocated_pvariant (hash, false) in
            (name, SumCase_allocated (selector, tuple_head tys))
        | [| ty |] ->
            let selector = CaseSel_allocated_pvariant (hash, true) in
            (name, SumCase_allocated (selector, tuple_head  [| ty |]))
        | _ -> invalid_arg "Dynamic.head: conjunction in polymorphic variant")
      (Array.to_list pvs) in
  { sum_desc = Pvariant pvs; sum_cases; }

(** *)

type _ head =
  | Int: int head
  | Nativeint: nativeint head
  | Int32: int32 head
  | Int64: int64 head
  | Char: char head
  | String: string head
  | Float: float head
  | Exn: exn head
  | Array: 'a ty -> 'a array head
  | Lazy: 'a ty ->  'a lazy_t head
  | Ty: 'a ty -> 'a ty head
  | Format6: ('a ty * 'b ty * 'c ty * 'd ty * 'e ty * 'f ty) ->
      ( ('a,'b,'c,'d,'e,'f) format6 ) head
  | Tuple: 'a tuple -> 'a head
  | Record: 'a record -> 'a head
  | Sum: 'a sum -> 'a head
  | Arrow: 'a ty * 'b ty -> ('a -> 'b) head
  | Opaque: 'a head

external untyped_head: 'a head -> CTy.dynamic_head = "%identity"
external typed_head: CTy.dynamic_head -> 'a head = "%identity"

let build_head ty : CTy.dynamic_head =
  match ty.CTy.desc with
  | CTy.DT_int -> untyped_head Int
  | CTy.DT_nativeint -> untyped_head Nativeint
  | CTy.DT_int32 -> untyped_head Int32
  | CTy.DT_int64 -> untyped_head Int64
  | CTy.DT_char -> untyped_head Char
  | CTy.DT_string -> untyped_head String
  | CTy.DT_float -> untyped_head Float
  | CTy.DT_exn -> untyped_head Exn
  | CTy.DT_array ty -> untyped_head (Array (CTy.ty ty))
  | CTy.DT_lazy ty -> untyped_head (Lazy (CTy.ty ty))
  | CTy.DT_ty ty -> untyped_head (Ty (CTy.ty ty))
  | CTy.DT_format6 (ty1, ty2, ty3, ty4, ty5, ty6) ->
      untyped_head (Format6 (CTy.ty ty1, CTy.ty ty2, CTy.ty ty3,
                          CTy.ty ty4, CTy.ty ty5, CTy.ty ty6))
  | CTy.DT_tuple el -> untyped_head (Tuple (tuple_head el))
  | CTy.DT_arrow (name,e1,e2) -> untyped_head (Arrow (CTy.ty e1,CTy.ty e2))
  | CTy.DT_pvariant { CTy.pvariant_constructors = pv } ->
      untyped_head (Sum (pvariant_head pv))
  | CTy.DT_unit | CTy.DT_option _ | CTy.DT_list _ | CTy.DT_bool
  | CTy.DT_constr _ ->
      let (id, params, desc) = CTy.instantiated_description ty in
      begin match desc with
      | CTy.DT_variant desc ->
          untyped_head (Sum (sum_head desc))
      | CTy.DT_record desc ->
          untyped_head (Record (record_head desc))
      | CTy.DT_abstract ->
          untyped_head Opaque
      | CTy.DT_alias _ -> assert false
      end
  | CTy.DT_var _ -> untyped_head Opaque
  | CTy.DT_univar -> untyped_head Opaque
  | CTy.DT_object -> untyped_head Opaque
  | CTy.DT_package -> untyped_head Opaque
  | CTy.DT_dummy -> untyped_head Opaque

let head (type t) (ty: t ty) : t head =
  let ty = CTy.expand_head (CTy.repr ty) in
  typed_head (CTy.build_dynamic_head build_head ty)

(** Association table *)

module type Typetable = sig

  type t
  type 'a elt

  type mode = [ `Default | `Strict | `Externals ]

  val create: int -> t

  val add: ?('a) -> t -> 'a elt -> unit

  module type Constr0 = sig
    type <transparent> constr
    val action : constr elt
  end
  val add0: t -> ?mode:mode -> ?resolve:bool -> (module Constr0) -> unit

  module type Constr1 = sig
    type <transparent> 'a constr
    val action : ?('a) -> 'a constr elt
  end
  val add1: t -> ?mode:mode -> ?resolve:bool -> (module Constr1) -> unit

  module type Constr2 = sig
    type <transparent> ('a, 'b) constr
    val action : ?('a) -> ?('b) -> ('a, 'b) constr elt
  end
  val add2: t -> ?mode:mode -> ?resolve:bool -> (module Constr2) -> unit

  (* ... *)

  val find: t -> 'a ty -> 'a elt

end

module Typetable(T : sig type 'a t end)
    : Typetable with type 'a elt = 'a T.t =
  struct

    type 'a elt = 'a T.t

    type mode = [ `Default | `Strict | `Externals ]

    module type Constr0 = sig
      type <transparent> constr
      val action : constr elt
    end
    module type Constr1 = sig
      type <transparent> 'a constr
      val action : ?('a) -> 'a constr elt
    end
    module type Constr2 = sig
      type <transparent> ('a, 'b) constr
      val action : ?('a) -> ?('b) -> ('a, 'b) constr elt
    end

    type action =
      | Action0 of (module Constr0)
      | Action1 of (module Constr1)
      | Action2 of (module Constr2)

    module PathTable = Hashtbl.Make(struct
      type t = CTy.path
      let equal p1 p2 = CTy.equal_path ~strict:true p1 p2
      let hash p = Hashtbl.hash p
    end)

    type t =
      { constrs: action PathTable.t;
        mutable types: (module Constr0) list }

    let create size = {
      constrs = PathTable.create size;
      types = [];
    }

    let rec simple_find : type t. (module Constr0) list -> t ty -> t elt =
      fun actions ty ->
      match actions with
      | [] -> raise Not_found
      | (module M) :: actions ->
          match eq (type M.constr) ty with
          | None -> simple_find actions ty
          | Some Eq -> M.action

    let extract_decl ty =
      match ty.CTy.desc with
      | CTy.DT_constr
          ({ CTy.params;
             CTy.body = CTy.DT_alias uty }, _, _) ->
               begin match CTy.extract_decl uty with
               | Some (decl, args)
                 when array_forall2 CTy.equal params args -> Some decl
               | _ -> None
               end
      | _ -> None

    let rec resolve_decl decl =
      match decl.CTy.body with
      | CTy.DT_variant _ | CTy.DT_record _ | CTy.DT_abstract -> decl
      | CTy.DT_alias uty ->
          match CTy.extract_decl uty with
          | Some (decl, args) when array_forall2 (==) args decl.CTy.params ->
              resolve_decl decl
          | _ -> invalid_arg "..."

    let rec add_constrs t
        ?(mode = (`Default : mode)) ?(resolve = false) decl action =
      match decl.CTy.body with
      | CTy.DT_variant _ | CTy.DT_record _ | CTy.DT_abstract ->
          if resolve then invalid_arg "Dynamic.Typetable.add: not an alias.";
          begin match mode with
          | `Default ->
              PathTable.add t.constrs decl.CTy.internal_name action;
              Array.iter (fun id -> PathTable.add t.constrs id action)
                decl.CTy.external_ids
          | `Strict ->
              PathTable.add t.constrs decl.CTy.internal_name action
          | `Externals ->
              Array.iter (fun id -> PathTable.add t.constrs id action)
                decl.CTy.external_ids
          end
      | CTy.DT_alias _ ->
          if resolve then
            add_constrs t ~mode (resolve_decl decl) action
          else
            begin match mode with
            | `Externals ->
                Array.iter (fun id -> PathTable.add t.constrs id action)
                  decl.CTy.external_ids
            | `Default | `Strict ->
                invalid_arg "Dynamic.Typetable.add: aliased type constructor.";
            end

    let add ?(type t) t (action: t elt) =
      let module M = struct
        type constr = t
        let constr = (type t)
        let action = action
      end in
      t.types <- (module M) :: t.types

    let add0 t ?mode ?resolve (module M : Constr0) =
      match extract_decl (CTy.repr (type M.constr)) with
      | None -> invalid_arg "Dynamic.Typetable.add0: not type constructor."
      | Some decl -> add_constrs t ?mode ?resolve decl (Action0 (module M))

    let add1 t ?mode ?resolve (module M : Constr1) =
      match extract_decl (CTy.repr (type dummy M.constr)) with
      | None -> invalid_arg "Typetable.add1: not a type constructor."
      | Some decl -> add_constrs t ?mode ?resolve decl (Action1 (module M))

    let add2 t ?mode ?resolve (module M : Constr2) =
      match extract_decl (CTy.repr (type (dummy, dummy) M.constr)) with
      | None -> invalid_arg "Typetable.add2: not a type constructor."
      | Some decl -> add_constrs t ?mode ?resolve decl (Action2 (module M))

    let find (type t) t (ty : t ty) : t elt =
      let uty = CTy.expand_head (CTy.repr ty) in
      match CTy.extract_decl uty with
      | Some (decl, args) ->
          begin try
            match PathTable.find t.constrs decl.CTy.internal_name with
            | Action0 (module M) ->
                (Obj.magic M.action)
            | Action1 (module M) ->
                (Obj.magic M.action : CTy.uty -> _)
                  args.(0)
            | Action2 (module M) ->
                (Obj.magic M.action : CTy.uty -> CTy.uty -> _)
                  args.(0) args.(1)
          with Not_found -> simple_find t.types ty
          end
      | None -> simple_find t.types ty

  end
