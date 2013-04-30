
open Asttypes
open Lambda
open Path
open Typedtree

(** Primitives (byterun/ty.c) *)

let new_expr_id_prim =
  Pccall
    Primitive.(
      {prim_name = "caml_ty_new_expr_id"; prim_arity = 1; prim_alloc = false;
       prim_native_name = ""; prim_native_float = false})

let new_coercion_id_prim =
  Pccall
    Primitive.(
      {prim_name = "caml_ty_new_coercion_id"; prim_arity = 1; prim_alloc = false;
       prim_native_name = ""; prim_native_float = false})

let new_expr_id = Lprim(new_expr_id_prim, [lambda_unit])
let new_coercion_id = Lprim(new_coercion_id_prim, [lambda_unit])

(** Helpers *)

let make_array l = Lprim (Pmakeblock (0, Mutable), l)

(** Compilation of Camlinternal.dynpath *)

let dynpath_dot p name =
  (* CamlinternalTy.Pdot (p, name) *)
  Lprim(Pmakeblock (1, Immutable), [p; Lconst (Const_immstring name)])
let dynpath_apply p1 p2 =
  (* CamlinternalTy.Papply (p1, p2) *)
  Lprim(Pmakeblock (2, Immutable), [p1; p2])

let rec transl_dynpath env = function
  | Pident id ->
      if Ident.global id then
        if !Clflags.native_code
        then Lprim(Pfield 0, [Lprim (Pgetglobal (Ident.dynpath id), [])])
        else Lprim(Pgetglobal (Ident.dynpath id), [])
      else Lvar (Ident.dynpath id)
  | Pdot(p, name, _) -> dynpath_dot (transl_dynpath env p) name
  | Papply(p1, p2) ->
      dynpath_apply (transl_dynpath env p1) (transl_module_id env p2)

and transl_module_id env p =
  transl_dynpath env (Env.find_module_dynid p env)

let dynpath_new_anonymous_id =
  (* CamlinternalTy.Pident (new_module_id, Anonymous) *)
  Lprim(Pmakeblock (0, Immutable),
        [new_coercion_id; Lconst (Const_base (Const_int 0))])

let dynpath_new_compunit_id name =
  (* CamlinternalTy.Pident (new_module_id, Compunit name) *)
  Lprim(Pmakeblock (0, Immutable),
        [new_coercion_id;
         Lprim(Pmakeblock (0, Immutable),
               [Lconst (Const_immstring name)])])

let dynpath_new_coercion_id env parent =
  match parent with
  | Some path ->
      (* CamlinternalTy.Pident (new_module_id, Coercion path) *)
      Lprim(Pmakeblock (0, Immutable),
            [new_coercion_id;
             Lprim(Pmakeblock (1, Immutable),
                   [transl_dynpath env path])])
  | None -> dynpath_new_anonymous_id

let rec transl_module_dynpath mexp =
  match mexp.mod_desc with
  | Tmod_ident (p,_) -> transl_module_id mexp.mod_env p
  | Tmod_apply(funct, arg, coercion) when !Clflags.applicative_functors ->
      dynpath_apply
        (transl_module_dynpath funct)
        (transl_module_dynpath arg)
  | _ -> dynpath_new_anonymous_id

let transl_dynpath_init ids =
  make_sequence (fun id ->
    let name = Ident.name id in
    Lambda.Lprim(Lambda.Psetglobal (Ident.dynpath id),
                  [dynpath_new_compunit_id name]))
    ids

let transl_dynpath_init_pack targetname names =
  let id = Ident.create_persistent targetname in
  make_sequence (fun name ->
    let fullname = targetname ^ "." ^ name in
    let modid = Ident.create_persistent fullname in
    Lambda.Lprim(Lambda.Psetglobal (Ident.dynpath modid),
                 [transl_dynpath Env.empty (Pdot (Pident id, name, nopos))]))
    names

(** Type expressions and type declarations *)

let transl_expr env loc ty = lambda_unit (* FIXME GRGR *)
