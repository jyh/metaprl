(*
 * Atom is the type of tokens (strings)
 *
 *)

include Itt_equal

open Printf
open Debug
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
 * $Log$
 * Revision 1.7  1998/06/22 19:46:12  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.6  1998/06/01 13:55:45  jyh
 * Proving twice one is two.
 *
 * Revision 1.5  1998/05/28 13:47:22  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.4  1998/04/24 02:43:21  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.3  1998/04/22 22:44:34  jyh
 * *** empty log message ***
 *
 * Revision 1.2  1997/08/06 16:18:23  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:07  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 * Revision 1.6  1996/09/25 22:52:10  jyh
 * Initial "tactical" commit.
 *
 * Revision 1.5  1996/05/21 02:16:33  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.4  1996/04/11 13:33:49  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.3  1996/03/28 02:51:26  jyh
 * This is an initial version of the type theory.
 *
 * Revision 1.2  1996/03/05 19:59:39  jyh
 * Version just before LogicalFramework.
 *
 * Revision 1.1  1996/02/13 21:35:53  jyh
 * Intermediate checkin while matching is bing added to the refiner.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
