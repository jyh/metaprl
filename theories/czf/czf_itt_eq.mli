(*
 * We define an equality on sets.
 * The normal intensional equality ('s1 = 's2 in set) is
 * not sufficient, because it is not a small type (it is in U2).
 *
 * We define and extensional equality by induction
 * on the sets.
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
 *)

include Czf_itt_set

open Refiner.Refiner.TermType

open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare eq{'s1; 's2}
declare eq_inner{'s1; 's2}
declare fun_set{z. 'f['z]}
declare fun_prop{z. 'P['z]}
declare dfun_prop{u. 'A['u]; x, y. 'B['x; 'y]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite reduce_eq_inner : eq_inner{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} <-->
   ((all y1 : 'T1. exst y2: 'T2. eq_inner{.'f1['y1]; .'f2['y2]})
    & (all y2 : 'T2. exst y1: 'T1. eq_inner{.'f1['y1]; .'f2['y2]}))

rewrite unfold_eq : eq{'s1; 's2} <-->
   ((isset{'s1} & isset{'s2}) & eq_inner{'s1; 's2})

rewrite reduce_eq : eq{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} <-->
   ((isset{collect{'T1; x1. 'f1['x1]}} & isset{collect{'T2; x2. 'f2['x2]}})
   & ((all y1 : 'T1. exst y2: 'T2. eq_inner{.'f1['y1]; .'f2['y2]})
     & (all y2 : 'T2. exst y1: 'T1. eq_inner{.'f1['y1]; .'f2['y2]})))

(*
 * A functional predicate can produce proofs for
 * all equal sets.
 *)
rewrite unfold_fun_set : fun_set{z. 'f['z]} <-->
    (all s1: set. all s2: set. (eq{'s1; 's2} => eq{'f['s1]; 'f['s2]}))

rewrite unfold_fun_prop : fun_prop{z. 'P['z]} <-->
    (all s1: set. all s2: set. (eq{'s1; 's2} => 'P['s1] => 'P['s2]))

rewrite unfold_dfun_prop : dfun_prop{u. 'A['u]; x, y. 'B['x; 'y]} <-->
  (all s1: set. all s2: set. (eq{'s1; 's2} => (u1: 'A['s1] -> 'B['s1; 'u1] -> u2: 'A['s2] -> 'B['s2; 'u2])))

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Membership in a universe.
 *)
axiom eq_inner_equality1 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- eq_inner{'s1; 's2} = eq_inner{'s1; 's2} in univ[1:l] }

(*
 * Membership in a universe.
 *)
axiom eq_inner_type 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- "type"{eq_inner{'s1; 's2}} }

(*
 * More general equality in a universe.
 *)
axiom eq_inner_equality2 'H :
   sequent [squash] { 'H >- 's1 = 's3 in set } -->
   sequent [squash] { 'H >- 's2 = 's4 in set } -->
   sequent ['ext] { 'H >- eq_inner{'s1; 's2} = eq_inner{'s3; 's4} in univ[1:l] }

(*
 * Functionality of eq_inner.
 *)
axiom eq_inner_fun 'H :
   sequent ['ext] { 'H >- fun_set{z. 'f1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f2['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. eq_inner{'f1['z]; 'f2['z]}} }

(*
 * Equality typehood.
 *)
axiom eq_type 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- "type"{eq{'s1; 's2}} }

(*
 * Equality is over sets.
 *)
axiom eq_isset_left 'H 's2 :
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- isset{'s1} }

axiom eq_isset_right 'H 's1 :
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- isset{'s2} }

(*
 * Reflexivity.
 *)
axiom eq_ref 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- eq{'s1; 's1} }

(*
 * Symettry.
 *)
axiom eq_sym 'H :
   sequent ['ext] { 'H >- eq{'s2; 's1} } -->
   sequent ['ext] { 'H >- eq{'s1; 's2} }

(*
 * Transitivity.
 *)
axiom eq_trans 'H 's2 :
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- eq{'s2; 's3} } -->
   sequent ['ext] { 'H >- eq{'s1; 's3} }

(*
 * Finally, functionality puts them all together.
 *)
axiom eq_fun 'H :
   sequent ['ext] { 'H >- fun_set{z. 'f1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f2['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. eq{'f1['z]; 'f2['z]}} }

(*
 * Substitution over functional expressions.
 *)
axiom eq_hyp_subst 'H 'J 's1 's2 (bind{v. 'P['v]}) 'z :
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x]; z: 'P['s2] >- 'C['x] } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- fun_prop{z. 'P['z]} } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- 'C['x] }

axiom eq_concl_subst 'H 's1 's2 (bind{v. 'C['v]}) 'z :
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- 'C['s2] } -->
   sequent ['ext] { 'H >- fun_prop{z. 'C['z]} } -->
   sequent ['ext] { 'H >- 'C['s1] }

(*
 * Typehood of fun propositions.
 *)
axiom fun_set_type 'H :
   sequent ['ext] { 'H; z: set >- isset{'f['z]} } -->
   sequent ['ext] { 'H >- "type"{fun_set{z. 'f['z]}} }

axiom fun_prop_type 'H :
   sequent [squash] { 'H; z: set >- "type"{'f['z]} } -->
   sequent ['ext] { 'H >- "type"{fun_prop{z. 'f['z]}} }

(*
 * Unquantified sets are functional.
 *)
axiom fun_set 'H :
   sequent ['ext] { 'H >- isset{'u} } -->
   sequent ['ext] { 'H >- fun_set{z. 'u} }

axiom fun_ref 'H :
   sequent ['ext] { 'H >- fun_set{z. 'z} }

(*
 * LEMMAS:
 * Every functional type is a type.
 *)
axiom fun_set_is_set 'H (bind{z. 'P['z]}) 's :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- fun_set{z. 'P['z]} } -->
   sequent ['ext] { 'H >- isset{'P['s]} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val is_eq_term : term -> bool
val mk_eq_term : term -> term -> term
val dest_eq : term -> term * term

val is_fun_set_term : term -> bool
val mk_fun_set_term : string -> term -> term
val dest_fun_set : term -> string * term

val is_fun_prop_term : term -> bool
val mk_fun_prop_term : string -> term -> term
val dest_fun_prop : term -> string * term

(*
 * Equality relations.
 *)
topval eqSetRefT : tactic
topval eqSetSymT : tactic
topval eqSetTransT : term -> tactic

(*
 * 's1 = 's2 => isset{'s1}
 *)
topval eqSetLeftT : term -> tactic

(*
 * 's1 = 's2 => isset{'s2}
 *)
topval eqSetRightT : term -> tactic

(*
 * Substitution.
 *)
topval setSubstT : term -> int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
