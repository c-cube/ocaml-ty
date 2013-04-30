(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Generation of bytecode from lambda terms *)

open Lambda
open Instruct

val compile_implementation: string -> lambda -> instruction list
val compile_phrase: lambda -> instruction list * instruction list
val compile_dynpath_init: Ident.t list -> instruction list
val compile_dynpath_init_pack: string -> string list -> instruction list
