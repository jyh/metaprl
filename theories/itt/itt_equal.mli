(*
 * This module defines thepreliminary basis for the type
 * theory, including "type", universes, and equality rules.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *
 *)

extends Base_theory
extends Itt_comment

open Basic_tactics

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "type"{'a}
declare univ[i:l]
declare equal{'T; 'a; 'b}
declare cumulativity[i:l, j:l]

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

topval reduce_cumulativity : conv

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
rule equalityAxiom 'H :
   sequent { <H>; x: 'T; <J['x]> >- 'x in 'T }

(*
 * Reflexivity.
 *)
rule equalityRef 'y :
   sequent { <H> >- 'x = 'y in 'T } -->
   sequent { <H> >- 'x in 'T }

(*
 * Symettry.
 *)
rule equalitySym :
   sequent { <H> >- 'y = 'x in 'T } -->
   sequent { <H> >- 'x = 'y in 'T }

(*
 * Transitivity.
 *)
rule equalityTrans 'z :
   sequent { <H> >- 'x = 'z in 'T } -->
   sequent { <H> >- 'z = 'y in 'T } -->
   sequent { <H> >- 'x = 'y in 'T }

(*
 * H >- type ext a = b in T
 * by equalityFormation T
 *
 * H >- T ext a
 * H >- T ext b
 *)
rule equalityFormation 'T :
   sequent { <H> >- 'T } -->
   sequent { <H> >- 'T } -->
   sequent { <H> >- univ[i:l] }

(*
 * H >- (a1 = b1 in T1) = (a2 = b2 in T2) in Ui
 * by equalityEquality
 *
 * H >- T1 = T2 in Ui
 * H >- a1 = a2 in T1
 * H >- b1 = b2 in T1
 *)
rule equalityEquality :
   sequent { <H> >- 'T1 = 'T2 in univ[i:l] } -->
   sequent { <H> >- 'a1 = 'a2 in 'T1 } -->
   sequent { <H> >- 'b1 = 'b2 in 'T1 } -->
   sequent { <H> >- ('a1 = 'b1 in 'T1) = ('a2 = 'b2 in 'T2) in univ[i:l] }

(*
 * Typehood.
 *)
rule equalityType :
   sequent { <H> >- 'a in 'T } -->
   sequent { <H> >- 'b in 'T } -->
   sequent { <H> >- "type"{. 'a = 'b in 'T } }

(*
 * H >- it in (a = b in T)
 * by axiomMember
 *
 * H >- a = b in T
 *)
rule axiomMember :
   sequent { <H> >- 'a = 'b in 'T } -->
   sequent { <H> >- it in ('a = 'b in 'T) }

rule type_axiomMember :
   sequent { <H> >- "type"{'T} } -->
   sequent { <H> >- it in "type"{'T} }

(*
 * H, x: a = b in T, J[x] >- C[x]
 * by equalityElimination i
 *
 * H, x: a = b in T; J[it] >- C[it]
 *)
rule equalityElimination 'H :
   sequent { <H>; 'a = 'b in 'T; <J[it]> >- 'C[it] } -->
   sequent { <H>; x: 'a = 'b in 'T; <J['x]> >- 'C['x] }

(*
 * H >- T = T in type
 * by typeEquality
 *
 * H >- T
 *)
rule typeEquality :
   sequent { <H> >- 'T } -->
   sequent { <H> >- "type"{'T} }

(*
 * H >- Uj in Ui
 * by universeMember (side (j < i))
 *)
rule universeMember :
   sequent { <H> >- cumulativity[j:l, i:l] } -->
   sequent { <H> >- univ[j:l] in univ[i:l] }

(*
 * H >- x = x in Ui
 * by universeCumulativity
 *
 * H >- x = x in Uj
 * H >- cumulativity(j, i)
 *)
rule universeCumulativity univ[j:l] :
   sequent { <H> >- cumulativity[j:l, i:l] } -->
   sequent { <H> >- 'x = 'y in univ[j:l] } -->
   sequent { <H> >- 'x = 'y in univ[i:l] }

(*
 * Universe is a type.
 *)
rule universeType :
   sequent { <H> >- "type"{univ[l:l]} }

(*
 * Anything in a universe is a type.
 *)
rule universeMemberType univ[i:l] :
   sequent { <H> >- 'x in univ[i:l] } -->
   sequent { <H> >- "type"{'x} }

(*
 * Derived form for known membership.
 *)
rule universeAssumType 'H :
   sequent { <H>; x: univ[l:l]; <J['x]> >- "type"{'x} }

(*
 * H >- Ui ext Uj
 * by universeFormation level{$j:l}
 *)
rule universeFormation univ[j:l] :
   sequent { <H> >- cumulativity[j:l, i:l] } -->
   sequent { <H> >- univ[i:l] }

(************************************************************************
 * PRIMITIVES AND TACTICS                                               *
 ************************************************************************)

val equal_term : term
val is_equal_term : term -> bool
val is_member_term : term -> bool
val complete_unless_member : Dtactic.intro_option
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

(* Universe inference functions *)
val infer_univ_dep0_dep0 : (term -> term * term) -> typeinf_comp
val infer_univ_dep0_dep1 : (term -> var * term * term) -> typeinf_comp
val infer_univ1 : typeinf_comp

val equality_prec : auto_prec

(*
 * Typehood from truth.
 *)
topval typeAssertT : tactic

(*
 * Turn an eqcd tactic into a d tactic.
 *)
topval equalRefT : term -> tactic
topval equalSymT : tactic
topval equalTransT : term -> tactic

topval univTypeT : term -> tactic
topval cumulativityT : term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
