(*
 * Subtype type.
 *
 *)

include Itt_equal

open Refiner.Refiner.Term

open Sequent
open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare subtype{'A; 'B}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_subtype

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext subtype(A; B)
 * by subtypeFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
axiom subtypeFormation 'H :
   sequent ['ext] { 'H >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- subtype(A1; B1) = subtype(A2; B2) in Ui
 * by subtypeEquality
 *
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
axiom subtypeEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- subtype{'A1; 'B1} = subtype{'A2; 'B2} in univ[@i:l] }

(*
 * H >- subtype(A; B) ext it
 * by subtype_axiomFormation
 *
 * H >- A = A in Ui
 * H; x: A; y: A; x = y in A >- x = y in B
 *)
axiom subtype_axiomFormation 'H 'x :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; x: 'A >- 'x = 'x in 'B } -->
   sequent ['ext] { 'H >- subtype{'A; 'B} }

(*
 * H >- it = it in subtype(A; B)
 * by subtype_axiomEquality
 *
 * H >- subtype(A; B)
 *)
axiom subtype_axiomEquality 'H :
   sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- it = it in subtype{'A; 'B} }

(*
 * H, x: subtype(A; B); J[x] >- C[x]
 * by subtypeElimination
 *
 * H, x: subtype(A; B); J[it] >- C[it]
 *)
axiom subtypeElimination 'H 'J :
   sequent ['ext] { 'H; x: subtype{'A; 'B}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: subtype{'A; 'B}; 'J['x] >- 'C['x] }

(*
 * H >- x = y in B
 * by subtypeElimination2 A
 *
 * H >- x = y in A
 * H >- subtype(A; B)
 *)
axiom subtypeElimination2 'H 'A :
   sequent [squash] { 'H >- 'x = 'y in 'A } -->
   sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- 'x = 'y in 'B }

(*
 * Squash elimination.
 *)
axiom subtype_squashElimination 'H :
   sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- subtype{'A; 'B} }

(************************************************************************
 * RESOURCE                                                             *
 ************************************************************************)

(*
 * Define a resource to keep track of proofs of subtyping.
 * This resource provides tactics to prove subtyping goals.
 * These tactics take transitivity into account, and try
 * to construct an optimal subtype chain.
 *)

(*
 * This is what is supplied to the resource.
 *)
type sub_info_type = (term * term) list * tactic

type sub_resource_info =
   LRSubtype of sub_info_type
 | RLSubtype of sub_info_type
 | DSubtype of sub_info_type

(*
 * Internal type.
 *)
type sub_data

(*
 * The resource itself.
 *)
resource (sub_resource_info, tactic, sub_data) sub_resource

(*
 * Utilities.
 *)
val subtypeT : tactic

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_subtype : int -> tactic
val eqcd_subtype : tactic

val is_subtype_term : term -> bool
val dest_subtype : term -> term * term
val mk_subtype_term : term -> term -> term

(*
 * $Log$
 * Revision 1.7  1998/07/02 18:37:59  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.6  1998/06/22 19:46:26  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.5  1998/06/01 13:56:28  jyh
 * Proving twice one is two.
 *
 * Revision 1.4  1998/05/28 13:48:16  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.3  1998/04/22 22:45:21  jyh
 * *** empty log message ***
 *
 * Revision 1.2  1997/08/06 16:18:46  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:29  jyh
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
 * Revision 1.4  1996/09/02 19:37:45  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.3  1996/05/21 02:17:20  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/04/11 13:34:22  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.1  1996/03/30 01:37:21  jyh
 * Initial version of ITT.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
