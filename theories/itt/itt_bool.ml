(*!
 * @spelling{bool ifthenelse splitBoolT splitITE}
 *
 * @begin[doc]
 * @module[Itt_bool]
 *
 * The @tt{Itt_bool} module defines a type of (decidable)
 * Booleans.  The definition of the Boolean values is
 * based on the @hrefterm[unit] type in the @hrefmodule[Itt_unit] module
 * and the @hrefterm[union] type in the @hrefmodule[Itt_union]
 * module, as the type $@union{@unit; @unit}$.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * @email{jyh@cs.cornell.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
extends Itt_equal
extends Itt_struct
extends Itt_union
extends Itt_set
extends Itt_logic
extends Itt_decidable
(*! @docoff *)

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Var

open Base_dtactic
open Base_auto_tactic

open Itt_equal
open Itt_struct
open Itt_squash
open Itt_logic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The following terms define the Boolean connectives.
 * The Boolean values are @emph{not} propositions; the
 * @tt{assert} term converts a Boolean expression
 * to propositional form.  Note that these connectives
 * are completely separate from the logical connectives
 * defined in @hrefmodule[Itt_logic].
 *
 * The $@bool$ type is defined as the type $@union{@unit; @unit}$.
 * The $@true$ term is chosen to be the @emph{left} term, and $@false$
 * is the @emph{right} term.
 * @end[doc]
 *)
define unfold_bool : bool <--> (unit + unit)
define unfold_btrue : btrue <--> inl{it}
define unfold_bfalse : bfalse <--> inr{it}

(*!
 * @begin[doc]
 * The @tt{ifthenelse} term is the program that
 * performs case analysis on a Boolean value.  The
 * @tt{ifthenelse} term is defined directly in terms
 * of the @hrefterm[decide] term in @hrefmodule[Itt_union].
 * The Boolean connectives are defined in terms of @tt{ifthenelse}.
 * @end[doc]
 *)
define unfold_ifthenelse : ifthenelse{'b; 'e1; 'e2} <--> decide{'b; x. 'e1; y.
 'e2}
define unfold_bor : bor{'a; 'b} <--> ifthenelse{'a; btrue; 'b}
define unfold_band : band{'a; 'b} <--> ifthenelse{'a; 'b; bfalse}
define unfold_bimplies : bimplies{'a; 'b} <--> ifthenelse{'a; 'b; btrue}
define unfold_bnot : bnot{'a} <--> ifthenelse{'a; bfalse; btrue}

(*!
 * @begin[doc]
 * The @emph{propositional} form of a Boolean value is
 * expressed as an equality judgment.
 * @end[doc]
 *)
define unfold_assert : "assert"{'t} <--> ('t = btrue in bool)
(*! @docoff *)

let fold_bool = makeFoldC << bool >> unfold_bool
let fold_btrue = makeFoldC << btrue >> unfold_btrue
let fold_bfalse = makeFoldC << bfalse >> unfold_bfalse
let fold_bor = makeFoldC << bor{'a; 'b} >> unfold_bor
let fold_band = makeFoldC << band{'a; 'b} >> unfold_band
let fold_bimplies = makeFoldC << bimplies{'a; 'b} >> unfold_bimplies
let fold_bnot = makeFoldC << bnot{'a} >> unfold_bnot
let fold_assert = makeFoldC << "assert"{'t} >> unfold_assert

(*!
 * @begin[doc]
 * The reductions on literal Booleans are derived
 * from the computational properties of the @hrefterm[union]
 * type.
 * @end[doc]
 *)
interactive_rw reduce_ifthenelse_true : ifthenelse{btrue; 'e1; 'e2} <--> 'e1
interactive_rw reduce_ifthenelse_false : ifthenelse{bfalse; 'e1; 'e2} <--> 'e2
(*! @docoff *)

let resource reduce +=
   [<< ifthenelse{btrue; 'e1; 'e2} >>, reduce_ifthenelse_true;
    << ifthenelse{bfalse; 'e1; 'e2} >>, reduce_ifthenelse_false]

(************************************************************************
 * REDUCTIONS                                                           *
 ************************************************************************)

(*! @doc{nil} *)
interactive_rw reduce_bnot_true : bnot{btrue} <--> bfalse

interactive_rw reduce_bnot_false : bnot{bfalse} <--> btrue

interactive_rw reduce_bor_true : bor{btrue; 'e1} <--> btrue

interactive_rw reduce_bor_false : bor{bfalse; 'e1} <--> 'e1

interactive_rw reduce_band_true : band{btrue; 'e1} <--> 'e1

interactive_rw reduce_band_false : band{bfalse; 'e1} <--> bfalse

interactive_rw reduce_bimplies_true : bimplies{btrue; 'e1} <--> 'e1

interactive_rw reduce_bimplies_false : bimplies{bfalse; 'e1} <--> btrue
(*! @docoff *)

let resource reduce +=
   [<< bnot{btrue} >>, reduce_bnot_true;
    << bnot{bfalse} >>, reduce_bnot_false;
    << bor{btrue; 'e1} >>, reduce_bor_true;
    << bor{bfalse; 'e1} >>, reduce_bor_false;
    << band{btrue; 'e1} >>, reduce_band_true;
    << band{bfalse; 'e1} >>, reduce_band_false;
    << bimplies{btrue; 'e1} >>, reduce_bimplies_true;
    << bimplies{bfalse; 'e1} >>, reduce_bimplies_false]

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

(*
 * Precedences:
 *
 * implies < or < and < not < assert
 *)
prec prec_bimplies
prec prec_bor
prec prec_band
prec prec_bnot
prec prec_assert

prec prec_bimplies < prec_bor
prec prec_bor < prec_band
prec prec_band < prec_bnot
prec prec_bnot < prec_assert

dform bool_df : except_mode[src] :: bool =
   `"Bool"

dform btrue_df : except_mode[src] :: btrue =
   `"true"

dform bfalse_df : except_mode[src] :: bfalse =
   `"false"

dform bor_df : parens :: "prec"[prec_bor] :: except_mode[src] :: bor{'a; 'b} =
   slot{'a} " " vee subb " " slot{'b}

dform band_df : parens :: "prec"[prec_band] :: except_mode[src] :: band{'a; 'b}
 =
   slot{'a} " " wedge subb " " slot{'b}

dform bimplies_df : parens :: "prec"[prec_bimplies] :: except_mode[src] ::
 bimplies{'a; 'b} =
   slot{'a} " " Rightarrow subb " " slot{'b}

dform bnot_df : parens :: "prec"[prec_bnot] :: except_mode[src] :: bnot{'a} =
   tneg subb slot{'a}

dform ifthenelse_df : parens :: "prec"[prec_bor] :: except_mode[src] ::
 ifthenelse{'e1; 'e2; 'e3} =
   math_if{'e1; 'e2; 'e3}

dform assert_df : parens :: "prec"[prec_assert] :: except_mode[src] ::
 "assert"{'t} =
   downarrow slot{'t}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Typehood, well-formedness, and membership}
 *
 * The $@bool$ type is a member of every universe, and it
 * contains the terms $@true$ and $@false$.
 * @end[doc]
 *)
interactive boolEquality {| intro []; eqcd |} 'H :
   sequent ['ext] { 'H >- "bool" in univ[i:l] }

interactive boolType {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{bool} }

interactive btrue_member {| intro []; eqcd |} 'H :
  sequent ['ext] { 'H >- btrue in "bool" }

interactive bfalse_member {| intro []; eqcd |} 'H :
   sequent ['ext] { 'H >- bfalse in "bool" }

(*!
 * @begin[doc]
 * @modsubsection{Elimination}
 *
 * The elimination rule performs a case analysis on a Boolean
 * assumption.  There are two cases: one where the assumption is
 * true, and another where it is false.
 * @end[doc]
 *)
interactive boolElimination2 {| elim [] |} 'H 'J 'x :
   [main] sequent['ext] { 'H; 'J[btrue] >- 'C[btrue] } -->
   [main] sequent['ext] { 'H; 'J[bfalse] >- 'C[bfalse] } -->
   sequent ['ext] { 'H; x: "bool"; 'J['x] >- 'C['x] }

(*!
 * @begin[doc]
 * @modsubsection{Combinator well-formedness}
 *
 * The @tt{ifthenelse} term computes a type if its
 * argument is Boolean, and its branches are types under
 * a case analysis on the condition.
 * @end[doc]
 *)
interactive ifthenelse_type2 {| intro [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- 'e in bool } -->
   [wf] sequent [squash] { 'H; x: 'e = btrue in bool >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; x: 'e = bfalse in bool >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{ifthenelse{'e; 'A; 'B}} }

(*!
 * @begin[doc]
 * @modsubsection{Contradiction}
 *
 * The two following rules represent proof by contradiction:
 * $@true$ and $@false$ are provably distinct.
 * @end[doc]
 *)
interactive boolContradiction1 {| elim [] |} 'H 'J :
   sequent ['ext] { 'H; x: btrue = bfalse in bool; 'J['x] >- 'C['x] }

interactive boolContradiction2 {| elim [] |} 'H 'J :
   sequent ['ext] { 'H; x: bfalse = btrue in bool; 'J['x] >- 'C['x] }

(*!
 * @begin[doc]
 * @modsubsection{Combinator equality}
 *
 * The @tt{ifthenelse} term computes a value of type $T$
 * if the condition is a Boolean value, and the branches
 * both have type $T$ under a case analysis on the
 * condition.
 * @end[doc]
 *)
interactive ifthenelse_equality {| intro []; eqcd |} 'H 'w :
   [wf] sequent [squash] { 'H >- 'e1 = 'e2 in bool } -->
   [wf] sequent [squash] { 'H; w: 'e1 = btrue in bool >- 'x1 = 'x2 in 'T } -->
   [wf] sequent [squash] { 'H; w: 'e1 = bfalse in bool >- 'y1 = 'y2 in 'T } -->
   sequent ['ext] { 'H >- ifthenelse{'e1; 'x1; 'y1} = ifthenelse{'e2; 'x2; 'y2}
 in 'T }

(*!
 * @begin[doc]
 * @modsubsection{Computational equivalence}
 *
 * The Boolean values are computationally equivalent
 * if they are equal.  This is because the @emph{only}
 * (canonical) terms in $@unit + @unit$ are the terms
 * $@inl{@it}$ ($@true$) and $@inr{@it}$ ($@false$).
 * @end[doc]
 *)
interactive boolSqequal 'H :
   sequent [squash] { 'H >- 'x = 'y in bool } -->
   sequent ['ext] { 'H >- 'x ~ 'y }
(*! @docoff *)

let d_bool_sqequalT p =
   boolSqequal (Sequent.hyp_count_addr p) p

let bool_sqequal_term1 = << 'e ~ btrue >>
let bool_sqequal_term2 = << 'e ~ bfalse >>
let bool_sqequal_term3 = << btrue ~ 'e >>
let bool_sqequal_term4 = << bfalse ~ 'e >>

let resource intro += [
   bool_sqequal_term1, wrap_intro d_bool_sqequalT;
   bool_sqequal_term2, wrap_intro d_bool_sqequalT;
   bool_sqequal_term3, wrap_intro d_bool_sqequalT;
   bool_sqequal_term4, wrap_intro d_bool_sqequalT
]

(*
 * H >- Ui ext Unit
 * by boolFormation
 *)
interactive boolFormation 'H :
   sequent ['ext] { 'H >- univ[i:l] }

(*
 * H >- Bool ext btrue
 * by bool_*Formation
 *)
interactive bool_trueFormation 'H :
   sequent ['ext] { 'H >- "bool" }

interactive bool_falseFormation 'H :
   sequent ['ext] { 'H >- "bool" }

(*!
 * @begin[doc]
 * @modsubsection{Connective well-formedness}
 *
 * The connectives are Boolean values if their
 * immediate subterms are also Boolean values.
 * @end[doc]
 *)
interactive bor_member {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 't1 in bool } -->
   [wf] sequent [squash] { 'H >- 't2 in bool } -->
   sequent ['ext] { 'H >- bor{'t1; 't2} in bool }

interactive band_member {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 't1 in bool } -->
   [wf] sequent [squash] { 'H >- 't2 in bool } -->
   sequent ['ext] { 'H >- band{'t1; 't2} in bool }

interactive bimplies_member {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 't1 in bool } -->
   [wf] sequent [squash] { 'H >- 't2 in bool } -->
   sequent ['ext] { 'H >- bimplies{'t1; 't2} in bool }

interactive bnot_equal {| intro []; eqcd |} 'H :
   [wf] sequent [squash] { 'H >- 'a = 'b in bool } -->
   sequent ['ext] { 'H >- bnot{'a} = bnot{'b} in bool }

(*!
 * @begin[doc]
 * @modsubsection{Propositional reasoning}
 *
 * The @emph{reasoning} about Boolean expressions
 * is performed using the @emph{propositional} form,
 * coded using the @hrefterm[assert] form.  The
 * @tt{assert} term is well-formed if its argument is
 * a Boolean value.
 *
 * The $@assert{@true}$ goal is always provable;
 * the $@assert{@false}$ assumption is contradictory.
 * @end[doc]
 *)
interactive assert_type {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 't in bool } -->
   sequent ['ext] { 'H >- "type"{."assert"{'t}} }

interactive assert_true {| intro [] |} 'H :
   sequent ['ext] { 'H >- "assert"{btrue} }

interactive assert_false {| elim [] |} 'H 'J :
   sequent ['ext] { 'H; x: "assert"{bfalse}; 'J['x] >- 'C['x] }

(*!
 * @begin[doc]
 * @modsubsection{Case analysis and substitution}
 *
 * The following two rules perform a case analysis
 * on a Boolean expression in a clause.  This reasoning
 * is allowed because the canonical Boolean terms
 * are just $@true$ and $@false$.
 * @end[doc]
 *)
interactive bool_subst_concl 'H bind{x. 'C['x]} 'e 'y :
   [wf] sequent [squash] { 'H >- 'e in bool } -->
   [main] sequent ['ext] { 'H; y: "assert"{'e} >- 'C[btrue] } -->
   [main] sequent ['ext] { 'H; y: "assert"{bnot{'e}} >- 'C[bfalse] } -->
   sequent ['ext] { 'H >- 'C['e] }

interactive bool_subst_hyp 'H 'J bind{x. 'A['x]} 'e 'y :
   [wf] sequent [squash] { 'H; x: 'A['e]; 'J['x] >- 'e in bool } -->
   [main] sequent ['ext] { 'H; x: 'A[btrue]; 'J['x]; y: "assert"{'e} >- 'C['x] }
 -->
   [main] sequent ['ext] { 'H; x: 'A[bfalse]; 'J['x]; y: "assert"{bnot{'e}} >-
 'C['x] } -->
   sequent ['ext] { 'H; x: 'A['e]; 'J['x] >- 'C['x] }

(*!
 * @begin[doc]
 * @modsubsection{Extensional membership}
 *
 * Two Boolean expressions $A$ and $B$ are equal if the
 * @misspelled{bi}-implication $A @Leftrightarrow_b B$ holds.
 * @end[doc]
 *)
interactive bool_ext_equality 'H 'u :
   [wf] sequent [squash] { 'H >- 'x in bool } -->
   [wf] sequent [squash] { 'H >- 'y in bool } -->
   [main] sequent [squash] { 'H; u: "assert"{'x} >- "assert"{'y} } -->
   [main] sequent [squash] { 'H; u: "assert"{'y} >- "assert"{'x} } -->
   sequent ['ext] { 'H >- 'x = 'y in bool }

(*!
 * @begin[doc]
 * @modsubsection{Squash reasoning}
 *
 * The proof extract of a Boolean assertion is always the
 * term $@it$ term; the proof itself can be omitted.
 * @end[doc]
 *)
interactive assertSquashElim {| squash; intro [] |} 'H :
   sequent [squash] { 'H >- "assert"{'t} } -->
   sequent ['ext] { 'H >- it in "assert"{'t} }

(*!
 * @begin[doc]
 * @modsubsection{Reasoning about the Boolean connectives}
 *
 * The following two rules define introduction and
 * elimination reasoning on the Boolean negation.
 * @end[doc]
 *)
interactive assert_bnot_intro {| intro [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- 't1 in bool } -->
   [main] sequent [squash] { 'H; x: "assert"{'t1} >- "false" } -->
   sequent ['ext] { 'H >- "assert"{bnot{'t1}} }

interactive assert_bnot_elim {| elim [] |} 'H 'J :
   [wf] sequent [squash] { 'H; 'J[it] >- "assert"{'t} } -->
   sequent ['ext] { 'H; x: "assert"{bnot{'t}}; 'J['x] >- 'C['x] }

(*!
 * @begin[doc]
 * The @tt{magic} rule defines classical reasoning about
 * Boolean values.  The rule can be used to prove $@neg@neg A @Rightarrow_b A$,
 * and it can be used to perform @emph{all} Boolean reasoning using
 * only the elimination rules.
 * @end[doc]
 *)
interactive assert_magic 'H 'x :
   [wf] sequent [squash] { 'H >- 't in bool } -->
   sequent [squash] { 'H; x: "assert"{bnot{'t}} >- "false" } -->
   sequent ['ext] { 'H >- "assert"{'t} }

(*!
 * @begin[doc]
 * The following rule establishes that @tt[assert] is always decidable.
 * @end[doc]
 *)
interactive assert_is_decidable {| intro [] |} 'H:
   [wf] sequent [squash] { 'H >- 't in bool } -->
   sequent ['ext] { 'H >- decidable{."assert"{'t}} }

(*!
 * @begin[doc]
 * The following four rules define elimination reasoning
 * on the Boolean binary connectives.
 * @end[doc]
 *)
interactive assert_bor_elim {| elim [] |} 'H 'J :
   [wf] sequent [squash] { 'H; x: "assert"{bor{'t1; 't2}}; 'J['x] >- 't1 in bool
 } -->
   [main] sequent ['ext] { 'H; x: "assert"{'t1}; 'J[it] >- 'C[it] } -->
   [main] sequent ['ext] { 'H; x: "assert"{'t2}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{bor{'t1; 't2}}; 'J['x] >- 'C['x] }

interactive assert_band_elim {| elim [] |} 'H 'J 'y 'z :
   [wf] sequent [squash] { 'H; x: "assert"{band{'t1; 't2}}; 'J['x] >- 't1 IN
 bool } -->
   [main] sequent ['ext] { 'H; y: "assert"{'t1}; z: "assert"{'t2}; 'J[it] >-
 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{band{'t1; 't2}}; 'J['x] >- 'C['x] }

interactive assert_bimplies_elim {| elim [] |} 'H 'J :
   [assertion] sequent [squash] { 'H; 'J[it] >- "assert"{'t1} } -->
   [main] sequent ['ext] { 'H; 'J[it]; y: "assert"{'t2} >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{bimplies{'t1; 't2}}; 'J['x] >- 'C['x] }

(*!
 * @begin[doc]
 * Finally, the following rules define
 * introduction reasoning on the Boolean propositional
 * connectives.
 * @end[doc]
 *)
interactive assert_bor_intro_left {| intro [SelectOption 1] |} 'H :
   [wf] sequent [squash] { 'H >- 't2 in bool } -->
   [main] sequent [squash] { 'H >- "assert"{'t1} } -->
   sequent ['ext] { 'H >- "assert"{bor{'t1; 't2}} }

interactive assert_bor_intro_right {| intro [SelectOption 2] |} 'H :
   [wf] sequent [squash] { 'H >- 't1 in bool } -->
   [main] sequent [squash] { 'H >- "assert"{'t2} } -->
   sequent ['ext] { 'H >- "assert"{bor{'t1; 't2}} }

interactive assert_band_intro {| intro [] |} 'H :
   [main] sequent [squash] { 'H >- "assert"{'t1} } -->
   [main] sequent [squash] { 'H >- "assert"{'t2} } -->
   sequent ['ext] { 'H >- "assert"{band{'t1; 't2}} }

interactive assert_bimplies_intro {| intro [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- 't1 in bool } -->
   [main] sequent [squash] { 'H; x: "assert"{'t1} >- "assert"{'t2} } -->
   sequent ['ext] { 'H >- "assert"{bimplies{'t1; 't2}} }

(*! @docoff *)

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Standard term.
 *)
let bool_term = << "bool" >>
let btrue_term = << btrue >>
let bfalse_term = << bfalse >>

let assert_term = << "assert"{'t} >>
let assert_opname = opname_of_term assert_term
let mk_assert_term = mk_dep0_term assert_opname
let is_assert_term = is_dep0_term assert_opname
let dest_assert = dest_dep0_term assert_opname

let ifthenelse_term = << ifthenelse{'e1; 'e2; 'e3} >>
let ifthenelse_opname = opname_of_term ifthenelse_term
let mk_ifthenelse_term = mk_dep0_dep0_dep0_term ifthenelse_opname
let is_ifthenelse_term = is_dep0_dep0_dep0_term ifthenelse_opname
let dest_ifthenelse = dest_dep0_dep0_dep0_term ifthenelse_opname

let bor_term = << bor{'a; 'b} >>
let bor_opname = opname_of_term bor_term
let is_bor_term = is_dep0_dep0_term bor_opname
let mk_bor_term = mk_dep0_dep0_term bor_opname
let dest_bor = dest_dep0_dep0_term bor_opname

let extBoolT p =
   let v = maybe_new_vars1 p "u" in
      bool_ext_equality (Sequent.hyp_count_addr p) v p

let d_magic_assertT p =
   let v = maybe_new_vars1 p "v" in
      assert_magic (Sequent.hyp_count_addr p) v p

let magicT = d_magic_assertT

(************************************************************************
 * BOOL SPLITTING                                                       *
 ************************************************************************)

(*!
 * @begin[doc]
 * @tactics
 *
 * @begin[description]
 * @item{@tactic[splitBoolT];
 *  { The @tt{splitBoolT} tactic performs a case analysis
 *    on a Boolean expression in a clause.  The tactic
 *    @tt{splitBoolT i e} produces three subgoals; it
 *    asserts that $e$ is actually a Boolean expression,
 *    and it produces two subgoals where the expression
 *    $e$ in clause $i$ is replaced with the terms $@true$
 *    and $@false$.}}
 * @end[description]
 * @docoff
 * @end[doc]
 *)

(*
 * Split a bool in the conclusion.
 *)
let splitBoolCT a p =
   let x = get_opt_var_arg "z" p in
   let bind =
      try
         let t1 = get_with_arg p in
            if is_xbind_term t1 then
               t1
            else
               raise (RefineError ("splitBoolT", StringTermError ("need a
 \"bind\" term: ", t1)))
      with
         RefineError _ ->
            mk_xbind_term x (var_subst (Sequent.concl p) a x)
   in
      bool_subst_concl (Sequent.hyp_count_addr p) bind a x p

(*
 * Split a bool in a hyp.
 *)
let splitBoolHT i a p =
   let z = get_opt_var_arg "z" p in
   let bind =
      try
         let b = get_with_arg p in
            if is_xbind_term b then
               b
            else
               raise (RefineError ("splitBoolT", StringTermError ("need a
 \"bind\" term: ", b)))
      with
         RefineError _ ->
            mk_xbind_term z (var_subst (Sequent.nth_hyp p i) a z)
   in
   let j, k = Sequent.hyp_indices p i in
      bool_subst_hyp j k bind a z p

let splitBoolT t i =
   if i = 0 then
      splitBoolCT t
   else
      splitBoolHT i t

(*
 * Split ifthenelse.
 *)
let search_ifthenelse goal =
   let rec search addrs vars addr goal =
      if is_ifthenelse_term goal then
         let t, _, _ = dest_ifthenelse goal in
            if is_some_var_free_list vars [t] then
               search_term addrs vars addr goal
            else
               search_term ((addr, t) :: addrs) vars addr goal
      else
         search_term addrs vars addr goal
   and search_term addrs vars addr goal =
      let { term_terms = bterms } = dest_term goal in
         search_bterms addrs vars (0 :: addr) bterms
   and search_bterms addrs vars addr = function
      bterm :: bterms ->
         let { bvars = bvars; bterm = bterm } = dest_bterm bterm in
         let addrs = search addrs (bvars @ vars) addr bterm in
         let addr =
            match addr with
               i :: t ->
                  succ i :: t
             | [] ->
                  raise (Invalid_argument "search_ifthenelse: empty address")
         in
            search_bterms addrs vars addr bterms
    | [] ->
         addrs
   in
      search [] [] [] goal

(*
 * Filter out all the addresses for the term.
 *)
let rec filter_ifthenelse t = function
   (addr, t') :: tl ->
      if alpha_equal t t' then
         List.rev addr :: filter_ifthenelse t tl
      else
         filter_ifthenelse t tl
 | [] ->
      []

(*
 * Reduce the ifthenelse true cases.
 *)
let rec reduce_ite_trueC = function
   addr :: addrs ->
      addrC addr reduce_ifthenelse_true thenC reduce_ite_trueC addrs
 | [] ->
      idC

let rec reduce_ite_falseC = function
   addr :: addrs ->
      addrC addr reduce_ifthenelse_false thenC reduce_ite_falseC addrs
 | [] ->
      idC

(*!
 * @begin[doc]
 * @begin[description]
 * @item{@tactic[splitITE];
 *  { The @tt{splitITE i} tactic searches for an occurrence
 *    of a subterm of the form $@if{t_1; t_2; t_3}$ in clause
 *    $i$, and generates two main subgoals, one for the case where
 *    $t_1$ is true and the conditional is replaced with $t_2$,
 *    and the other where $t_1$ is false and the conditional is
 *    replaced with the term $t_3$.}}
 * @end[description]
 * @docoff
 * @end[doc]
 *)
let splitITE i p =
   let t =
      if i = 0 then
         Sequent.concl p
      else
         Sequent.nth_hyp p i
   in
   let addrs = search_ifthenelse t in
   let t =
      try get_with_arg p with
         RefineError _ ->
            match addrs with
               (_, t) :: _ ->
                  t
             | [] ->
                  raise (RefineError ("search_ifthenelse", StringError "no free
 ifthenelse"))
   in
   let addrs = filter_ifthenelse t addrs in
   let _ =
      if addrs = [] then
         raise (RefineError ("splitITE", StringTermError ("no condition", t)))
   in
   let i'= if (i>=0) then i else pred i in
      (splitBoolT t i
       thenLT [idT;
               rw (reduce_ite_trueC addrs) i';
               rw (reduce_ite_falseC addrs) i']) p

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of Bool and bool constants
 *)
let inf_b = Typeinf.infer_const bool_term

let resource typeinf += [
   bool_term, infer_univ1;
   btrue_term, inf_b;
   bfalse_term, inf_b;
]

(***********************************************************************
 * ADDITIONAL FACTS                                                    *
 ***********************************************************************)

interactive_rw reduce_bnot_bnot :
   ( 'e1 in bool ) -->
   bnot{bnot{'e1}} <--> 'e1

let reduce_bnot_bnotC = reduce_bnot_bnot

interactive eq_bfalse2assert {| intro []; eqcd |} 'H :
   [wf] sequent ['ext] { 'H >- 'e1 in bool } -->
   [main] sequent ['ext] { 'H >- "assert"{bnot{'e1}} } -->
   sequent ['ext] { 'H >- 'e1 = bfalse in bool }

let eq_bfalse2assertT i p = eq_bfalse2assert (Sequent.clause_addr p i) p

interactive assert2eq_bfalse 'H :
   [main] sequent ['ext] { 'H >- 'e1 = bfalse in bool } -->
   sequent ['ext] { 'H >- "assert"{bnot{'e1}} }

let assert2eq_bfalseT i p = assert2eq_bfalse (Sequent.clause_addr p i) p

interactive_rw reduce_band_same :
   ( 'e in bool ) -->
   band{'e;'e} <--> 'e

interactive_rw reduce_bor_same :
   ( 'e in bool ) -->
   bor{'e;'e} <--> 'e

let resource reduce +=
   [<< bnot{bnot{'e}} >>, reduce_bnot_bnot;
    << band{'e; 'e} >>, reduce_band_same;
    << bor{'e; 'e} >>, reduce_bor_same;
   ]
(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
