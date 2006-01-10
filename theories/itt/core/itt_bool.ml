doc <:doc<
   @module[Itt_bool]

   The @tt[Itt_bool] module defines a type of (decidable)
   Booleans.  The definition of the Boolean values is
   based on the @hrefterm[unit] type in the @hrefmodule[Itt_unit] module
   and the @hrefterm[union] type in the @hrefmodule[Itt_union]
   module, as the type $@union{@unit; @unit}$.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998 Jason Hickey, Cornell University

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

   Author: Jason Hickey
   @email{jyh@cs.cornell.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_equal
extends Itt_struct
extends Itt_union
extends Itt_set
extends Itt_logic
extends Itt_decidable
extends Itt_sqsimple
doc docoff

open Basic_tactics

open Itt_struct
open Itt_equal
open Itt_squash
open Itt_sqsimple

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @terms

   The following terms define the Boolean connectives.
   The Boolean values are @emph{not} propositions; the
   @tt[assert] term converts a Boolean expression
   to propositional form.  Note that these connectives
   are completely separate from the logical connectives
   defined in @hrefmodule[Itt_logic].

   The $@bool$ type is defined as the type $@union{@unit; @unit}$.
   The $@true$ term is chosen to be the @emph{left} term, and $@false$
   is the @emph{right} term.
>>
define unfold_bool : bool <--> (unit + unit)
define unfold_btrue : btrue <--> inl{it}
define unfold_bfalse : bfalse <--> inr{it}

doc <:doc<
   The @tt{ifthenelse} term is the program that
   performs case analysis on a Boolean value.  The
   @tt{ifthenelse} term is defined directly in terms
   of the @hrefterm[decide] term in @hrefmodule[Itt_union].
   The Boolean connectives are defined in terms of @tt{ifthenelse}.
>>
define unfold_ifthenelse : ifthenelse{'b; 'e1; 'e2} <--> decide{'b; x. 'e1; y. 'e2}
define unfold_bor : bor{'a; 'b} <--> ifthenelse{'a; btrue; 'b}
define unfold_band : band{'a; 'b} <--> ifthenelse{'a; 'b; bfalse}
define unfold_bimplies : bimplies{'a; 'b} <--> ifthenelse{'a; 'b; btrue}
define unfold_bnot : bnot{'a} <--> ifthenelse{'a; bfalse; btrue}

doc <:doc<
   The @emph{propositional} form of a Boolean value is
   expressed as an equality judgment.
>>
define unfold_assert : "assert"{'t} <--> ('t = btrue in bool)
doc docoff

let fold_bool = makeFoldC << bool >> unfold_bool
let fold_btrue = makeFoldC << btrue >> unfold_btrue
let fold_bfalse = makeFoldC << bfalse >> unfold_bfalse
let fold_bor = makeFoldC << bor{'a; 'b} >> unfold_bor
let fold_band = makeFoldC << band{'a; 'b} >> unfold_band
let fold_bimplies = makeFoldC << bimplies{'a; 'b} >> unfold_bimplies
let fold_bnot = makeFoldC << bnot{'a} >> unfold_bnot
let fold_assert = makeFoldC << "assert"{'t} >> unfold_assert

doc <:doc<
   The reductions on literal Booleans are derived
   from the computational properties of the @hrefterm[union]
   type.
>>
interactive_rw reduce_ifthenelse_true {| reduce |} : ifthenelse{btrue; 'e1; 'e2} <--> 'e1
interactive_rw reduce_ifthenelse_false {| reduce |} : ifthenelse{bfalse; 'e1; 'e2} <--> 'e2

(************************************************************************
 * REDUCTIONS                                                           *
 ************************************************************************)

interactive_rw reduce_bnot_true {| reduce |} : bnot{btrue} <--> bfalse

interactive_rw reduce_bnot_false {| reduce |} : bnot{bfalse} <--> btrue

interactive_rw reduce_bor_true {| reduce |} : bor{btrue; 'e1} <--> btrue

interactive_rw reduce_bor_false {| reduce |} : bor{bfalse; 'e1} <--> 'e1

interactive_rw reduce_band_true {| reduce |} : band{btrue; 'e1} <--> 'e1

interactive_rw reduce_band_false {| reduce |} : band{bfalse; 'e1} <--> bfalse

interactive_rw reduce_bimplies_true {| reduce |} : bimplies{btrue; 'e1} <--> 'e1

interactive_rw reduce_bimplies_false {| reduce |} : bimplies{bfalse; 'e1} <--> btrue
doc docoff

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

dform bool_df : except_mode[src]  :: except_mode[prl] :: bool =
   mathbbB

dform bool_df : mode[prl] :: bool =
   `"Bool"

dform btrue_df : except_mode[src] :: btrue =
   `"true"

dform bfalse_df : except_mode[src] :: bfalse =
   `"false"

dform bor_df : parens :: "prec"[prec_bor] :: except_mode[src] :: bor{'a; 'b} =
   slot{'a} " " vee subb " " slot{'b}

dform band_df : parens :: "prec"[prec_band] :: except_mode[src] :: band{'a; 'b} =
   szone pushm[0] slot{'a} hspace wedge subb " " slot{'b} popm ezone

dform bimplies_df : parens :: "prec"[prec_bimplies] :: except_mode[src] :: bimplies{'a; 'b} =
   slot{'a} " " Rightarrow subb " " slot{'b}

dform bnot_df : parens :: "prec"[prec_bnot] :: except_mode[src] :: bnot{'a} =
   tneg subb slot{'a}

dform ifthenelse_df : parens :: "prec"[prec_bor] :: except_mode[src] :: ifthenelse{'e1; 'e2; 'e3} =
   math_if{'e1; 'e2; 'e3}

dform assert_df : parens :: "prec"[prec_assert] :: except_mode[src] :: "assert"{'t} =
   uparrow slot{'t}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Typehood, well-formedness, and membership}

   The $@bool$ type is a member of every universe, and it
   contains the terms $@true$ and $@false$.
>>
interactive boolEquality {| intro [] |} :
   sequent { <H> >- "bool" in univ[i:l] }

interactive boolType {| intro [] |} :
   sequent { <H> >- "type"{bool} }

interactive btrue_member {| intro [] |} :
  sequent { <H> >- btrue in "bool" }

interactive bfalse_member {| intro [] |} :
   sequent { <H> >- bfalse in "bool" }

doc <:doc<
   @modsubsection{Elimination}

   The elimination rule performs a case analysis on a Boolean
   assumption.  There are two cases: one where the assumption is
   true, and another where it is false.
>>
interactive boolElimination2 {| elim [] |} 'H :
   [main] sequent{ <H>; <J[btrue]> >- 'C[btrue] } -->
   [main] sequent{ <H>; <J[bfalse]> >- 'C[bfalse] } -->
   sequent { <H>; x: "bool"; <J['x]> >- 'C['x] }
doc docoff

interactive_rw reduce_bor_true2 {| reduce |} :
   ('e1 in bool) -->
   bor{'e1; btrue} <--> btrue

doc <:doc<
   @modsubsection{Combinator well-formedness}

   The @tt{ifthenelse} term computes a type if its
   argument is Boolean, and its branches are types under
   a case analysis on the condition.
>>
interactive ifthenelse_type2 {| intro [] |} :
   [wf] sequent { <H> >- 'e in bool } -->
   [wf] sequent { <H>; x: 'e = btrue in bool >- "type"{'A} } -->
   [wf] sequent { <H>; x: 'e = bfalse in bool >- "type"{'B} } -->
   sequent { <H> >- "type"{ifthenelse{'e; 'A; 'B}} }

doc <:doc<
   @modsubsection{Contradiction}

   The two following rules represent proof by contradiction:
   $@true$ and $@false$ are provably distinct.
>>
interactive boolContradiction1 {| elim [] |} 'H :
   sequent { <H>; x: btrue = bfalse in bool; <J['x]> >- 'C['x] }

interactive boolContradiction2 {| elim [] |} 'H :
   sequent { <H>; x: bfalse = btrue in bool; <J['x]> >- 'C['x] }

doc <:doc<
   @modsubsection{Combinator equality}

   The @tt{ifthenelse} term computes a value of type $T$
   if the condition is a Boolean value, and the branches
   both have type $T$ under a case analysis on the
   condition.
>>
interactive ifthenelse_equality {| intro [] |} :
   [wf] sequent { <H> >- 'e1 = 'e2 in bool } -->
   [wf] sequent { <H>; w: 'e1 = btrue in bool >- 'x1 = 'x2 in 'T } -->
   [wf] sequent { <H>; w: 'e1 = bfalse in bool >- 'y1 = 'y2 in 'T } -->
   sequent { <H> >- ifthenelse{'e1; 'x1; 'y1} = ifthenelse{'e2; 'x2; 'y2}
 in 'T }

doc <:doc<
   @modsubsection{Computational equivalence}

   The Boolean values are computationally equivalent
   if they are equal.  This is because the @emph{only}
   (canonical) terms in $@unit + @unit$ are the terms
   $@inl{@it}$ ($@true$) and $@inr{@it}$ ($@false$).
>>
interactive boolSqequal {| nth_hyp |} :
   sequent { <H> >- 'x = 'y in bool } -->
   sequent { <H> >- 'x ~ 'y }

interactive sqsimple_bool {| intro []; sqsimple |} :
   sequent { <H> >- sqsimple{bool} }
doc docoff

let resource intro += [
   << 'e ~ btrue >>, wrap_intro boolSqequal;
   << 'e ~ bfalse >>, wrap_intro boolSqequal;
   << btrue ~ 'e >>, wrap_intro boolSqequal;
   << bfalse ~ 'e >>, wrap_intro boolSqequal
]

doc <:doc<
   @modsubsection{Connective well-formedness}

   The connectives are Boolean values if their
   immediate subterms are also Boolean values.
>>
interactive bor_member {| intro [] |} :
   [wf] sequent { <H> >- 't1 in bool } -->
   [wf] sequent { <H> >- 't2 in bool } -->
   sequent { <H> >- bor{'t1; 't2} in bool }

interactive band_member {| intro [] |} :
   [wf] sequent { <H> >- 't1 in bool } -->
   [wf] sequent { <H>; "assert"{'t1} >- 't2 in bool } -->
   sequent { <H> >- band{'t1; 't2} in bool }

interactive bimplies_member {| intro [] |} :
   [wf] sequent { <H> >- 't1 in bool } -->
   [wf] sequent { <H>; "assert"{'t1} >- 't2 in bool } -->
   sequent { <H> >- bimplies{'t1; 't2} in bool }

interactive bnot_equal {| intro [] |} :
   [wf] sequent { <H> >- 'a = 'b in bool } -->
   sequent { <H> >- bnot{'a} = bnot{'b} in bool }

doc <:doc<
   @modsubsection{Propositional reasoning}

   The @emph{reasoning} about Boolean expressions
   is performed using the @emph{propositional} form,
   coded using the @hrefterm[assert] form.  The
   @tt{assert} term is well-formed if its argument is
   a Boolean value.

   The <<"assert"{"true"}>> goal is always provable;
   the <<"assert"{"false"}>> assumption is contradictory.
>>
interactive assert_type {| intro [] |} :
   [wf] sequent { <H> >- 't in bool } -->
   sequent { <H> >- "type"{"assert"{'t}} }

interactive assert_univ {| intro [] |} :
   [wf] sequent { <H> >- 't in bool } -->
   sequent { <H> >- "assert"{'t} in univ[i:l] }

interactive assert_true {| intro [] |} :
   sequent { <H> >- "assert"{btrue} }

interactive assert_false {| elim []; nth_hyp |} 'H :
   sequent { <H>; x: "assert"{bfalse}; <J['x]> >- 'C['x] }

doc <:doc<
   @modsubsection{Case analysis and substitution}

   The following two rules perform a case analysis
   on a Boolean expression in a clause.  This reasoning
   is allowed because the canonical Boolean terms
   are just $@true$ and $@false$.
>>
interactive bool_subst_concl bind{x. 'C['x]} 'e :
   [wf] sequent { <H> >- 'e in bool } -->
   [main] sequent { <H>; y: "assert"{'e} >- 'C[btrue] } -->
   [main] sequent { <H>; y: "assert"{bnot{'e}} >- 'C[bfalse] } -->
   sequent { <H> >- 'C['e] }

interactive bool_subst_hyp 'H bind{x. 'A['x]} 'e :
   [wf] sequent { <H>; x: 'A['e]; <J['x]> >- 'e in bool } -->
   [main] sequent { <H>; x: 'A[btrue]; <J['x]>; y: "assert"{'e} >- 'C['x]
 }
 -->
   [main] sequent { <H>; x: 'A[bfalse]; <J['x]>; y: "assert"{bnot{'e}} >-
 'C['x] } -->
   sequent { <H>; x: 'A['e]; <J['x]> >- 'C['x] }

doc <:doc<
   @modsubsection{Extensional membership}

   Two Boolean expressions $A$ and $B$ are equal if the
   @misspelled{bi}-implication $A @Leftrightarrow_b B$ holds.
>>
interactive bool_ext_equality :
   [wf] sequent { <H> >- 'x in bool } -->
   [wf] sequent { <H> >- 'y in bool } -->
   [main] sequent { <H>; u: "assert"{'x} >- "assert"{'y} } -->
   [main] sequent { <H>; u: "assert"{'y} >- "assert"{'x} } -->
   sequent { <H> >- 'x = 'y in bool }

doc <:doc<
   @modsubsection{Squash reasoning}

   The proof extract of a Boolean assertion is always the
   term $@it$ term; the proof itself can be omitted.
>>
interactive assertSquashElim {| squash; intro [] |} :
   sequent { <H> >- "assert"{'t} } -->
   sequent { <H> >- it in "assert"{'t} }

doc <:doc<
   @modsubsection{Reasoning about the Boolean connectives}

   The following two rules define introduction and
   elimination reasoning on the Boolean negation.
>>
interactive assert_bnot_intro {| intro [] |} :
   [wf] sequent { <H> >- 't1 in bool } -->
   [main] sequent { <H>; x: "assert"{'t1} >- "false" } -->
   sequent { <H> >- "assert"{bnot{'t1}} }

interactive assert_bnot_elim {| elim [] |} 'H :
   [main] sequent { <H>; <J[it]> >- "assert"{'t} } -->
   sequent { <H>; x: "assert"{bnot{'t}}; <J['x]> >- 'C['x] }

doc <:doc<
   The @tt{magic} rule defines classical reasoning about
   Boolean values.  The rule can be used to prove $@neg@neg A @Rightarrow_b A$,
   and it can be used to perform @emph{all} Boolean reasoning using
   only the elimination rules.
>>
interactive assert_magic :
   [wf] sequent { <H> >- 't in bool } -->
   sequent { <H>; x: "assert"{bnot{'t}} >- "false" } -->
   sequent { <H> >- "assert"{'t} }

doc <:doc<
   The following rule establishes that @tt[assert] is always decidable.
>>
interactive assert_is_decidable {| intro [] |} :
   [wf] sequent { <H> >- 't in bool } -->
   sequent { <H> >- decidable{"assert"{'t}} }

doc <:doc<
   The following four rules define elimination reasoning
   on the Boolean binary connectives.
>>
interactive assert_bor_elim {| elim [] |} 'H :
   [wf] sequent { <H>; x: "assert"{bor{'t1; 't2}}; <J['x]> >- 't1 in
 bool
 } -->
   [main] sequent { <H>; x: "assert"{'t1}; <J[it]> >- 'C[it] } -->
   [main] sequent { <H>; x: "assert"{'t2}; <J[it]> >- 'C[it] } -->
   sequent { <H>; x: "assert"{bor{'t1; 't2}}; <J['x]> >- 'C['x] }

interactive assert_band_elim {| elim [] |} 'H :
   [wf] sequent { <H>; x: "assert"{band{'t1; 't2}}; <J['x]> >- 't1 IN
 bool } -->
   [main] sequent { <H>; y: "assert"{'t1}; z: "assert"{'t2}; <J[it]> >-
 'C[it] } -->
   sequent { <H>; x: "assert"{band{'t1; 't2}}; <J['x]> >- 'C['x] }

interactive assert_bimplies_elim {| elim [] |} 'H :
   [assertion] sequent { <H>; <J[it]> >- "assert"{'t1} } -->
   [main] sequent { <H>; <J[it]>; y: "assert"{'t2} >- 'C[it] } -->
   sequent { <H>; x: "assert"{bimplies{'t1; 't2}}; <J['x]> >- 'C['x] }

doc <:doc<
   Finally, the following rules define
   introduction reasoning on the Boolean propositional
   connectives.
>>
interactive assert_bor_intro_left {| intro [SelectOption 1] |} :
   [wf] sequent { <H> >- 't2 in bool } -->
   [main] sequent { <H> >- "assert"{'t1} } -->
   sequent { <H> >- "assert"{bor{'t1; 't2}} }

interactive assert_bor_intro_right {| intro [SelectOption 2] |} :
   [wf] sequent { <H> >- 't1 in bool } -->
   [main] sequent { <H> >- "assert"{'t2} } -->
   sequent { <H> >- "assert"{bor{'t1; 't2}} }

interactive assert_band_intro {| intro [] |} :
   [main] sequent { <H> >- "assert"{'t1} } -->
   [main] sequent { <H>; x: "assert"{'t1} >- "assert"{'t2} } -->
   sequent { <H> >- "assert"{band{'t1; 't2}} }

interactive assert_bimplies_intro {| intro [] |} :
   [wf] sequent { <H> >- 't1 in bool } -->
   [main] sequent { <H>; x: "assert"{'t1} >- "assert"{'t2} } -->
   sequent { <H> >- "assert"{bimplies{'t1; 't2}} }

doc docoff

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

let band_term = << band{'a; 'b} >>
let band_opname = opname_of_term band_term
let is_band_term = is_dep0_dep0_term band_opname
let mk_band_term = mk_dep0_dep0_term band_opname
let dest_band = dest_dep0_dep0_term band_opname

let extBoolT = bool_ext_equality
let magicT = assert_magic

(************************************************************************
 * BOOL SPLITTING                                                       *
 ************************************************************************)

doc <:doc<
   @tactics

   @begin[description]
   @item{@tactic[splitBoolT];
    { The @tt{splitBoolT} tactic performs a case analysis
      on a Boolean expression in a clause.  The tactic
      @tt{splitBoolT i e} produces three subgoals; it
      asserts that $e$ is actually a Boolean expression,
      and it produces two subgoals where the expression
      $e$ in clause $i$ is replaced with the terms $@true$
      and $@false$.}}
   @end[description]
   @docoff
>>

(*
 * Split a bool in the conclusion.
 *)
let splitBoolCT = argfunT (fun a p ->
   let bind = get_bind_from_arg_or_concl_subst p a in
      bool_subst_concl bind a)

(*
 * Split a bool in a hyp.
 *)
let splitBoolHT i a = funT (fun p ->
   let bind = get_bind_from_arg_or_hyp_subst p i a in
      bool_subst_hyp (Sequent.get_pos_hyp_num p i) bind a)

let splitBoolT t i =
   if i = 0 then
      splitBoolCT t
   else
      splitBoolHT i t

(*
 * Split ifthenelse.
 *)
let search_ifthenelse t vars  =
   (is_ifthenelse_term t) &&
   let t, _, _ = dest_ifthenelse t in
      not (SymbolSet.intersectp vars (free_vars_set t))

(*
 * Filter out all the addresses for the term.
 *)
let rec filter_ifthenelse term t vars =
   (is_ifthenelse_term t) &&
      let t, _, _ = dest_ifthenelse t in
         (alpha_equal t term) && not (SymbolSet.intersectp vars (free_vars_set t))

(*
 * Reduce the ifthenelse true cases.
 *)
let rec reduce_ite_trueC = function
   addr :: addrs ->
      addrLiteralC addr reduce_ifthenelse_true thenC reduce_ite_trueC addrs
 | [] ->
      idC

let rec reduce_ite_falseC = function
   addr :: addrs ->
      addrLiteralC addr reduce_ifthenelse_false thenC reduce_ite_falseC addrs
 | [] ->
      idC

doc <:doc<
   @begin[description]
   @item{@tactic[splitITE];
    { The @tt{splitITE i} tactic searches for an occurrence
      of a subterm of the form $@if{t_1; t_2; t_3}$ in clause
      $i$, and generates two main subgoals, one for the case where
      $t_1$ is true and the conditional is replaced with $t_2$,
      and the other where $t_1$ is false and the conditional is
      replaced with the term $t_3$.}}
   @end[description]
   @docoff
>>
let splitITE = argfunT (fun i p ->
   let term =
      if i = 0 then
         Sequent.concl p
      else
         Sequent.nth_hyp p i
   in
   let t =
      try get_with_arg p with
         RefineError _ ->
            match find_subterm term search_ifthenelse with
               addr :: _ ->
                  let t, _, _ = dest_ifthenelse (term_subterm term addr) in t
             | [] ->
                  raise (RefineError ("search_ifthenelse", StringError "no free ifthenelse"))
   in
   let addrs = find_subterm term (filter_ifthenelse t) in
   let () =
      if addrs = [] then
         raise (RefineError ("splitITE", StringTermError ("no condition", t)))
   in
   let i'= if (i>=0) then i else pred i in
      splitBoolT t i
       thenLT [idT;
               rw (reduce_ite_trueC addrs) i';
               rw (reduce_ite_falseC addrs) i'])

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

interactive_rw reduce_bnot_bnot {| reduce |} :
   ( 'e1 in bool ) -->
   bnot{bnot{'e1}} <--> 'e1

let reduce_bnot_bnotC = reduce_bnot_bnot

interactive eq_bfalse2assert {| intro [] |} :
   [wf] sequent { <H> >- 'e1 in bool } -->
   [main] sequent { <H> >- "assert"{bnot{'e1}} } -->
   sequent { <H> >- 'e1 = bfalse in bool }

let eq_bfalse2assertT = eq_bfalse2assert

interactive eq_bfalse2assert_elim {| elim [ThinOption thinT] |} 'H :
   [main] sequent { <H>; x: 'e1 = bfalse in bool; <J['x]>; "assert"{bnot{'e1}} >- 'C['x] } -->
   sequent { <H>; x: 'e1 = bfalse in bool; <J['x]> >- 'C['x] }

interactive assert2eq_bfalse :
   [main] sequent { <H> >- 'e1 = bfalse in bool } -->
   sequent { <H> >- "assert"{bnot{'e1}} }

interactive not_bnot_elim {| elim [ThinOption thinT] |} 'H :
   sequent { <H>; x: "not"{"assert"{bnot{'b}}}; <J['x]> >- 'b in bool } -->
   sequent { <H>; x: "not"{"assert"{bnot{'b}}}; "assert"{'b}; <J['x]> >- 'C['x] } -->
   sequent { <H>; x: "not"{"assert"{bnot{'b}}}; <J['x]> >- 'C['x] }

let assert2eq_bfalseT = assert2eq_bfalse

interactive not_assert_intro {| intro [] |} :
   [wf] sequent { <H> >- 'b in bool } -->
   [main] sequent { <H> >- "assert"{bnot{'b}} } -->
   sequent { <H> >- not{"assert"{'b}} }

interactive_rw reduce_band_same {| reduce |} :
   ( 'e in bool ) -->
   band{'e;'e} <--> 'e

interactive_rw reduce_bor_same {| reduce |} :
   ( 'e in bool ) -->
   bor{'e;'e} <--> 'e

interactive bandSym {| intro [] |} :
   [wf] sequent { <H> >- 'a in bool } -->
   [wf] sequent { <H> >- 'b in bool } -->
   sequent { <H> >- band{'a;'b}=band{'b;'a} in bool }

interactive boolMoveToConcl 'H :
   [wf] sequent { <H> >- 'B in bool } -->
   [wf] sequent { <H>; <J> >- 'C in bool } -->
	[main] sequent { <H>; <J> >- "assert"{bimplies{'B; 'C}} } -->
	sequent { <H>; "assert"{'B}; <J> >- "assert"{'C} }

interactive xor_property :
   [wf] sequent { <H> >- 'a in bool } -->
   [wf] sequent { <H> >- 'b in bool } -->
	sequent { <H> >- "assert"{bnot{band{'a;'b}}} } -->
	sequent { <H> >- "assert"{bor{'a;'b}} } -->
	sequent { <H> >- bnot{'a}='b in bool }

interactive_rw xor_property_rw 'b :
   ('a in bool) -->
   ('b in bool) -->
	("assert"{bnot{band{'a;'b}}}) -->
	("assert"{bor{'a;'b}}) -->
	bnot{'a} <--> 'b

let xor_propertyC = xor_property_rw

(*
 * H >- Ui ext Unit
 * by boolFormation
 *)
interactive boolFormation :
   sequent { <H> >- univ[i:l] }

(*
 * H >- Bool ext btrue
 * by bool_*Formation
 *)
interactive bool_trueFormation {| intro [] |} :
   sequent { <H> >- "bool" }

interactive bool_falseFormation :
   sequent { <H> >- "bool" }

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
