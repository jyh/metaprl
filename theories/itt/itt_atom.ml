(*
 * Atom is the type of tokens (strings)
 *
 *)

include Itt_equal

open Printf
open Nl_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Rformat
open Sequent
open Resource

open Itt_equal

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_atom%t" eflush

(* debug_string DebugLoad "Loading itt_atom..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare atom
declare token[@t:t]

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform atom_df : mode[prl] :: atom = `"Atom"
dform token_df : mode[prl] :: token[@t:t] =
   slot[@t:s]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Atom
 * by atomFormation
 *)
prim atomFormation 'H : : sequent ['ext] { 'H >- univ[@i:l] } = atom

(*
 * H >- Atom = Atom in Ui ext Ax
 * by atomEquality
 *)
prim atomEquality 'H : : sequent ['ext] { 'H >- atom = atom in univ[@i:l] } = it

(*
 * H >- Atom ext "t"
 * by tokenFormation "t"
 *)
prim tokenFormation 'H token[@t:t] : : sequent ['ext] { 'H >- atom } =
   token[@t:t]

(*
 * H >- "t" = "t" in Atom
 * by tokenEquality
 *)
prim tokenEquality 'H : : sequent ['ext] { 'H >- token[@t:t] = token[@t:t] in atom } = it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let atom_term = << atom >>
let token_term = << token[@x:t] >>
let token_opname = opname_of_term token_term
let is_token_term = TermOp.is_token_term token_opname
let dest_token = TermOp.dest_token_term token_opname
let mk_token_term = TermOp.mk_token_term token_opname

(*
 * D
 *)
let bogus_token = << token["token":t] >>

let d_atomT i p =
   if i = 0 then
      tokenFormation (num_hyps (goal p)) bogus_token p
   else
      failwith "Can't eliminate Atom"

let d_resource = d_resource.resource_improve d_resource (atom_term, d_atomT)

(*
 * EqCD.
 *)
let eqcd_atomT p =
   let count = num_hyps (goal p) in
      atomEquality count p

let eqcd_tokenT p =
   let count = hyp_count p in
      tokenEquality count p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (atom_term, eqcd_atomT)
let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (token_term, eqcd_tokenT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of atom.
 *)
let inf_atom _ decl _ = decl, univ1_term

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (atom_term, inf_atom)

(*
 * Type of an equality is the type of the equality type.
 *)
let inf_token _ decl _ = decl, atom_term

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (token_term, inf_token)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
