(*
 * This module defines thepreliminary basis for the type
 * theory, including "type", universes, and equality rules.
 *
 *)

include Tacticals

include Base_theory

include Itt_squash

open Refiner.Refiner.Term
open Tacticals
open Base_theory

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "type"{'a}
declare univ[@i:l]
declare equal{'T; 'a; 'b}
declare it

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_type
prec prec_equal

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood is equality.
 *)
axiom equalityAxiom 'H 'J :
   sequent ['ext] { 'H; x: 'T; 'J['x] >- 'x = 'x in 'T }

(*
 * Reflexivity.
 *)
axiom equalityRef 'H 'y :
   sequent ['ext] { 'H >- 'x = 'y in 'T } -->
   sequent ['ext] { 'H >- 'x = 'x in 'T }

(*
 * Symettry.
 *)
axiom equalitySym 'H :
   sequent ['ext] { 'H >- 'y = 'x in 'T } -->
   sequent ['ext] { 'H >- 'x = 'y in 'T }

(*
 * Transitivity.
 *)
axiom equalityTrans 'H 'z :
   sequent ['ext] { 'H >- 'x = 'z in 'T } -->
   sequent ['ext] { 'H >- 'z = 'y in 'T } -->
   sequent ['ext] { 'H >- 'x = 'y in 'T }

(*
 * H >- type ext a = b in T
 * by equalityFormation T
 *
 * H >- T ext a
 * H >- T ext b
 *)
axiom equalityFormation 'H 'T :
   sequent ['ext] { 'H >- 'T } -->
   sequent ['ext] { 'H >- 'T } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- (a1 = b1 in T1) = (a2 = b2 in T2) in Ui
 * by equalityEquality
 *
 * H >- T1 = T2 in Ui
 * H >- a1 = a2 in T1
 * H >- b1 = b2 in T1
 *)
axiom equalityEquality 'H :
   sequent [squash] { 'H >- 'T1 = 'T2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'a1 = 'a2 in 'T1 } -->
   sequent [squash] { 'H >- 'b1 = 'b2 in 'T2 } -->
   sequent ['ext] { 'H >- ('a1 = 'b1 in 'T1) = ('a2 = 'b2 in 'T2) in univ[@i:l] }

(*
 * Typehood.
 *)
axiom equalityType 'H :
   sequent [squash] { 'H >- 'a = 'a in 'T } -->
   sequent [squash] { 'H >- 'b = 'b in 'T } -->
   sequent ['ext] { 'H >- "type"{. 'a = 'b in 'T } }

(*
 * H >- it = it in (a = b in T)
 * by axiomEquality
 *
 * H >- a = b in T
 *)
axiom axiomEquality 'H :
   sequent [squash] { 'H >- 'a = 'b in 'T } -->
   sequent ['ext] { 'H >- it = it in ('a = 'b in 'T) }

(*
 * H, x: a = b in T, J[x] >- C[x]
 * by equalityElimination i
 *
 * H, x: a = b in T; J[it] >- C[it]
 *)
axiom equalityElimination 'H 'J :
   sequent ['ext] { 'H; x: 'a = 'b in 'T; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: 'a = 'b in 'T; 'J['x] >- 'C['x] }

(*
 * H >- T = T in type
 * by typeEquality
 *
 * H >- T
 *)
axiom typeEquality 'H :
   sequent [squash] { 'H >- 'T } -->
   sequent ['ext] { 'H >- "type"{'T} }

(*
 * Squash elim.
 *)
axiom equality_squashElimination 'H :
   sequent [squash] { 'H >- 'a = 'b in 'T } -->
   sequent ['ext] { 'H >- 'a = 'b in 'T }

(*
 * H >- Uj = Uj in Ui
 * by universeEquality (side (j < i))
 *)
mlterm cumulativity{univ[@j:l]; univ[@i:l]}

axiom universeEquality 'H :
   cumulativity{univ[@j:l]; univ[@i:l]} -->
   sequent ['ext] { 'H >- univ[@j:l] = univ[@j:l] in univ[@i:l] }

(*
 * H >- Ui ext Uj
 * by universeFormation level{$j:l}
 *)
axiom universeFormation 'H univ[@j:l] :
   cumulativity{univ[@j:l]; univ[@i:l]} -->
   sequent ['ext] {'H >- univ[@i:l] }

(*
 * Squash from any.
 *)
axiom squashFromAny 'H 'ext :
   sequent ['ext] { 'H >- 'T } -->
   sequent [squash] { 'H >- 'T }

(************************************************************************
 * EQCD TACTIC                                                          *
 ************************************************************************)

type eqcd_data

resource (term * tactic, tactic, eqcd_data) eqcd_resource

val eqcdT : tactic

(************************************************************************
 * PRIMITIVES AND TACTICS                                               *
 ************************************************************************)

val equal_term : term
val is_equal_term : term -> bool
val dest_equal : term -> term * term * term
val mk_equal_term : term -> term -> term -> term

val type_term : term
val is_type_term : term -> bool
val mk_type_term : term -> term
val dest_type_term : term -> term

val univ_term : term
val univ1_term : term
val is_univ_term : term -> bool
val dest_univ : term -> level_exp
val mk_univ_term : level_exp -> term

val it_term : term

val d_equalT : int -> tactic
val eqcd_univT : tactic
val eqcd_itT : tactic
val squash_equalT : tactic

(*
 * Turn an eqcd tactic into a d tactic.
 *)
val d_wrap_eqcd : tactic -> int -> tactic

val unsquashT : term -> tactic
val equalAssumT : int -> tactic
val equalRefT : term -> tactic
val equalSymT : tactic
val equalTransT : term -> tactic

(*
 * $Log$
 * Revision 1.8  1998/07/02 18:37:31  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.7  1998/06/22 19:46:16  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.6  1998/06/01 13:55:51  jyh
 * Proving twice one is two.
 *
 * Revision 1.5  1998/05/28 13:47:32  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.4  1998/04/22 22:44:44  jyh
 * *** empty log message ***
 *
 * Revision 1.3  1998/02/18 18:46:57  jyh
 * Initial ocaml semantics.
 *
 * Revision 1.2  1997/08/06 16:18:27  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:10  jyh
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
 * Revision 1.8  1996/10/23 15:18:07  jyh
 * First working version of dT tactic.
 *
 * Revision 1.7  1996/09/25 22:52:12  jyh
 * Initial "tactical" commit.
 *
 * Revision 1.6  1996/09/02 19:37:23  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.5  1996/05/21 02:16:45  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.4  1996/04/11 13:33:58  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.3  1996/03/30 01:37:13  jyh
 * Initial version of ITT.
 *
 * Revision 1.2  1996/03/28 02:51:30  jyh
 * This is an initial version of the type theory.
 *
 * Revision 1.1  1996/03/05 19:59:44  jyh
 * Version just before LogicalFramework.
 *
 * Revision 1.1  1996/02/13 21:36:01  jyh
 * Intermediate checkin while matching is bing added to the refiner.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
