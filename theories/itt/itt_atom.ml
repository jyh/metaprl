(*
 * Atom is the type of tokens (strings)
 *
 *)

open Debug
open Term
open Rformat
open Sequent
open Resource

include Itt_equal

(* debug_string DebugLoad "Loading itt_atom..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare atom
declare token[@t:t]

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform mode[prl] :: atom = `"Atom"
mldform mode[prl] :: token[@t:t] print_term buf =
   format_quoted_string buf t

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
     
(*
 * D
 *)
let atom_term = << atom >>

let bogus_token = << token["hello world":t] >>

let d_atom i p =
   if i = 0 then
      tokenFormation (num_hyps (goal p)) bogus_token p
   else
      failwith "Can't eliminate Atom"

let d_resource = d_resource.resource_improve d_resource (atom_term, d_atom)
let dT = d_resource.resource_extract d_resource

(*
 * EqCD.
 *)
let eqcd_atom p =
   let count = num_hyps (goal p) in
      atomEquality count p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (atom_term, eqcd_atom)
let eqcd = eqcd_resource.resource_extract eqcd_resource

(*
 * $Log$
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
