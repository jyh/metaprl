(*
 * This interpretation of CZF is derived from Aczel's
 * paper "The Type Theoretic Interpretation of Constructive
 * Set Theory: Inductive Definitions," Logic, Methodology
 * and Philosophy of Science VII, Barcan Marcus et. al. eds.,
 * Elsevier 1986 17--49.
 *
 * The "set" type is used to relate CZF to the Nuprl type theory.
 * We use a W-type over U1 to define sets.
 *
 *    type set = W(x:U1. x)
 *
 * We abbreviate the sets themselves as:
 *    collect{T; x. a[x]} = tree{T; lambda x. a[x]}
 *
 * This interpretation justifies Aczel's construction:
 *
 *          H >- T in small     H, x:T >- a[x] in set
 *          -----------------------------------------
 *               H >- collect{T; x. a[x]} in set
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

include Itt_theory

open Refiner.Refiner.Term

open Tacticals
open Conversionals

open Base_auto_tactic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * Sets are built by collecting over small types.
 *   set: the type of all sets
 *   is_pre_set{'s}: the judgement that 's is a set
 *   collect{'T; x. 'a['x]}:
 *      the set constructed from the family of sets 'a['x]
 *      where 'x ranges over 'T
 *   set_ind is the induction combinator.
 *)
declare pre_set
declare is_pre_set{'s}
declare collect{'T; x. 'a['x]}
declare set_ind{'s; x, f, g. 'b['x; 'f; 'g]}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

(*
 * Sets.
 *)
rewrite unfold_pre_set : pre_set <--> w{univ[1:l]; x. 'x}
rewrite unfold_is_pre_set : is_pre_set{'s} <--> ('s = 's in pre_set)
rewrite unfold_collect : collect{'T; x. 'a['x]} <--> tree{'T; lambda{x. 'a['x]}}
rewrite unfold_set_ind : set_ind{'s; x, f, g. 'b['x; 'f; 'g]} <-->
   tree_ind{'s; x, f, g. 'b['x; 'f; 'g]}

rewrite reduce_set_ind :
   set_ind{collect{'T; x. 'a['x]}; a, f, g. 'b['a; 'f; 'g]}
   <--> 'b['T; lambda{x. 'a['x]}; lambda{a2. lambda{b2. set_ind{.'a['a2] 'b2; a, f, g. 'b['a; 'f; 'g]}}}]

val fold_pre_set : conv
val fold_is_pre_set : conv
val fold_collect : conv
val fold_set_ind : conv

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * A set is a type in ITT.
 *)
rule pre_set_type 'H :
   sequent ['ext] { 'H >- "type"{pre_set} }

(*
 * Equality from sethood.
 *)
rule equal_pre_set 'H :
   sequent ['ext] { 'H >- is_pre_set{'s} } -->
   sequent ['ext] { 'H >- 's = 's in pre_set }

(*
 * By assumption.
 *)
rule is_pre_set_assum 'H 'J :
   sequent ['ext] { 'H; x: pre_set; 'J['x] >- is_pre_set{'x} }

(*
 * This is how a set is constructed.
 *)
rule is_pre_set_collect 'H 'y :
   sequent [squash] { 'H >- 'T = 'T in univ[1:l] } -->
   sequent [squash] { 'H; y: 'T >- is_pre_set{'a['y]} } -->
   sequent ['ext] { 'H >- is_pre_set{collect{'T; x. 'a['x]}} }

(*
 * Applications often come up.
 * This is not a necessary axiom, ut it is useful.
 *)
rule is_pre_set_apply 'H 'J :
   sequent [squash] { 'H; f: 'T -> pre_set; 'J['f] >- 'x = 'x in 'T } -->
   sequent ['ext] { 'H; f: 'T -> pre_set; 'J['f] >- is_pre_set{.'f 'x} }

(*
 * Induction.
 *)
rule pre_set_elim 'H 'J 'a 'T 'f 'w 'z :
   sequent ['ext] { 'H;
                    a: pre_set;
                    'J['a];
                    T: univ[1:l];
                    f: 'T -> pre_set;
                    w: (all x : 'T. 'C['f 'x]);
                    z: is_pre_set{collect{'T; x. 'f 'x}}
                  >- 'C[collect{'T; x. 'f 'x}]
                  } -->
                     sequent ['ext] { 'H; a: pre_set; 'J['a] >- 'C['a] }

(*
 * Equality on tree induction forms.
 *)
rule pre_set_ind_equality 'H 'A (bind{x.'B['x]}) 'a 'f 'g :
   sequent [squash] { 'H >- 'z1 = 'z2 in pre_set } -->
   sequent [squash] { 'H; a: 'A; f: 'B['a] -> pre_set; g: a: 'A -> 'B['a] -> 'T >-
      'body1['a; 'f; 'g] = 'body2['a; 'f; 'g] in 'T } -->
   sequent ['ext] { 'H >- set_ind{'z1; a1, f1, g1. 'body1['a1; 'f1; 'g1]}
                          = set_ind{'z2; a2, f2, g2. 'body2['a2; 'f2; 'g2]}
                          in 'T }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * is_pre_set{'s} => 's = 's in set
 *)
val eqPreSetT : tactic

(*
 * H, x: set, J >- is_pre_set{x}
 *)
val preSetAssumT : int -> tactic

(*
 * Automation.
 *)
val pre_set_prec : auto_prec

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
