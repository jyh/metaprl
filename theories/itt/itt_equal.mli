(*
 * This module defines thepreliminary basis for the type
 * theory, including "type", universes, and equality rules.
 *
 *)

open Term

include Tactic_type

include Base_theory

include Itt_squash

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "type"{'a}
declare univ[@i:l]
declare equal{'T; 'a; 'b}
declare it

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- type ext a = b in T
 * by equalityFormation T
 *
 * H >- T ext a
 * H >- T ext b
 *)
axiom equalityFormation 'H 'T :
   sequent [ext] { 'H >- 'T } -->
   sequent [ext] { 'H >- 'T } -->
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

(************************************************************************
 * EQCD TACTIC                                                          *
 ************************************************************************)

type eqcd_data
     
resource (term * tactic, tactic, eqcd_data) eqcd_resource

val eqcd_of_proof : tactic_arg -> tactic

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

val is_equal_term : term -> bool
val dest_equal : term -> term * term * term
val mk_equal_term : term -> term -> term -> term

(************************************************************************
 * PRIMITIVES AND TACTICS                                               *
 ************************************************************************)

val equal_term : term
val is_equal_term : term -> bool
val dest_equal : term -> term * term * term
val mk_equal_term : term -> term -> term -> term

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
 * $Log$
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
