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

extends Itt_theory
extends Czf_itt_comment

open Lm_symbol
open Refiner.Refiner.Term

open Tactic_type.Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * Sets are built by collecting over small types.
 *   set: the type of all sets
 *   isset{'s}: the judgement that 's is a set
 *   collect{'T; x. 'a['x]}:
 *      the set constructed from the family of sets 'a['x]
 *      where 'x ranges over 'T
 *   set_ind is the induction combinator.
 *)
declare set
declare isset{'s}
declare collect{'T; x. 'a['x]}
declare set_ind{'s; x, f, g. 'b['x; 'f; 'g]}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

(*
 * Sets.
 *)
rewrite unfold_set : set <--> w{univ[1:l]; x. 'x}
rewrite unfold_isset : isset{'s} <--> ('s = 's in set)
rewrite unfold_collect : collect{'T; x. 'a['x]} <--> tree{'T; lambda{x. 'a['x]}}
rewrite unfold_set_ind : set_ind{'s; x, f, g. 'b['x; 'f; 'g]} <-->
   tree_ind{'s; x, f, g. 'b['x; 'f; 'g]}

rewrite reduce_set_ind :
   set_ind{collect{'T; x. 'A['x]}; a, f, g. 'b['a; 'f; 'g]}
   <--> 'b['T; lambda{x. 'A['x]}; lambda{a2. set_ind{.'A['a2]; a, f, g. 'b['a; 'f; 'g]}}]

topval fold_set : conv
topval fold_isset : conv
topval fold_collect : conv
topval fold_set_ind : conv

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * A set is a type in ITT.
 *)
rule set_type :
   sequent { <H> >- "type"{set} }

(*
 * Equality from sethood.
 *)
rule equal_set :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- 's = 's in set }

(*
 * By assumption.
 *)
rule isset_assum 'H :
   sequent { <H>; x: set; <J['x]> >- isset{'x} }

(*
 * This is how a set is constructed.
 *)
rule isset_collect :
   sequent { <H> >- 'T = 'T in univ[1:l] } -->
   sequent { <H>; y: 'T >- isset{'a['y]} } -->
   sequent { <H> >- isset{collect{'T; x. 'a['x]}} }

(*
 * Induction.
 *)
rule set_elim 'H :
   sequent { <H>;
                    a: set;
                    <J['a]>;
                    T: univ[1:l];
                    f: 'T -> set;
                    w: (all x : 'T. 'C['f 'x]);
                    z: isset{collect{'T; x. 'f 'x}}
                  >- 'C[collect{'T; x. 'f 'x}]
                  } -->
                     sequent { <H>; a: set; <J['a]> >- 'C['a] }

(*
 * These are related forms to expand a set into its
 * collect representation.
 *)
rule set_split_hyp 'H 's (bind{v. 'A['v]}) :
   sequent { <H>; x: 'A['s]; <J['x]> >- isset{'s} } -->
   sequent { <H>; x: 'A['s]; <J['x]>; z: set >- "type"{'A['z]} } -->
   sequent { <H>;
                    x: 'A['s];
                    <J['x]>;
                    T: univ[1:l];
                    f: 'T -> set;
                    z: 'A[collect{'T; y. 'f 'y}]
                    >- 'C['z] } -->
   sequent { <H>; x: 'A['s]; <J['x]> >- 'C['x] }

rule set_split_concl 's (bind{v. 'C['v]}) :
   sequent { <H> >- isset{'s} } -->
   sequent { <H>; z: set >- "type"{'C['z]} } -->
   sequent { <H>; T: univ[1:l]; f: 'T -> set >- 'C[collect{'T; y. 'f 'y}] } -->
   sequent { <H> >- 'C['s] }

(*
 * Equality on tree induction forms.
rule set_ind_equality2 'a 'f 'g 'x :
   sequent { <H> >- 'z1 = 'z2 in set } -->
   sequent { <H>; a: univ[1:l]; f: 'a -> set; g: x: univ[1:l] -> 'x -> 'T >-
      'body1['a; 'f; 'g] = 'body2['a; 'f; 'g] in 'T } -->
   sequent { <H> >- set_ind{'z1; a1, f1, g1. 'body1['a1; 'f1; 'g1]}
                          = set_ind{'z2; a2, f2, g2. 'body2['a2; 'f2; 'g2]}
                          in 'T }
 *)

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val isset_term : term
val is_isset_term : term -> bool
val mk_isset_term : term -> term
val dest_isset : term -> term

val set_ind_term : term
val is_set_ind_term : term -> bool
val mk_set_ind_term : var -> var -> var -> term -> term -> term
val dest_set_ind : term -> var * var * var * term * term

(*
 * isset{'s} => 's = 's in set
 *)
topval eqSetT : tactic

(*
 * H, x: set, J >- isset{x}
 *)
topval setAssumT : int -> tactic

(*
 * Replace a set with a collect.
 *)
topval splitT : term -> int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
