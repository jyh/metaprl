doc <:doc<
   @module[Base_reflection_hoas]

   The @tt[Base_reflection_hoas] module formalizes operator constants
   and defines computational operations on them by exposing some of
   the system internals to the user.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2004 MetaPRL Group

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

   Author: Xin Yu @email{xiny@cs.caltech.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>
extends Perv
extends Shell_theory
extends Top_conversionals
doc docoff

open Basic_tactics

open Lm_debug
open Lm_symbol
open Lm_printf

open Term_sig
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermType
open Refiner.Refiner.TermMan
open Refiner.Refiner.Rewrite
open Refiner.Refiner.RefineError
open Dform
open Lm_rformat

(************************************************************************
 * List utilities.
 *)

(*
 * Lists.
 *)
let rnil_term = << rnil >>
let rnil_opname = opname_of_term rnil_term
let is_rnil_term = alpha_equal rnil_term

let rcons_term = << rcons{'a; 'b} >>
let rcons_opname = opname_of_term rcons_term

let is_rcons_term = is_dep0_dep0_term rcons_opname
let mk_rcons_term = mk_dep0_dep0_term rcons_opname
let dest_rcons = dest_dep0_dep0_term rcons_opname

let rec is_rlist_term t =
   is_rnil_term t || (is_rcons_term t && is_rlist_term (snd (dest_rcons t)))

let rec dest_rlist t =
   if is_rnil_term t then
      []
   else
      let hd, tl = dest_rcons t in
         hd :: (dest_rlist tl)

let rec mk_rlist_term = function
   h::t ->
      mk_rcons_term h (mk_rlist_term t)
 | [] ->
      rnil_term

(* ***
  let hyp_of_var v =
   Hypothesis(v, <<term>>)
*)
let get_var = function
   Hypothesis (v, term) -> v
 | Context (v, conts, subterms) ->
      raise (Invalid_argument "Base_reflection.get_bterm_var: bterm cannot have contexts as hypotheses")

doc <:doc<
   @modsection{Computational Operations on Operators}
   @modsubsection{@tt[If_quoted_op]}

   << if_quoted_op{'op; 'tt} >> evaluates to << 'tt >> when << 'op >> is a
   quoted operator and must fail to evaluate otherwise.
>>

declare if_quoted_op{'op; 'tt}

doc <:doc<
   << fake_mlrw[reduce_if_quoted_op]{
         if_quoted_op{
            <:doc<@underline{<<'op>>}@{@ldots@}>>; 'tt};
         'tt} >>
   @docoff
>>
ml_rw reduce_if_quoted_op {| reduce |} : ('goal :  if_quoted_op{ 't; 'tt }) =
   let t, tt = two_subterms goal in
   let t' = unquote_term t in
      tt

doc <:doc<
   @modsubsection{@tt[Shape]}

   << shape{'op} >> is a list of natural numbers that are meant to represent
   the number of bindings in each of the operator's arguments. The length of
   the list is the operator's arity.
>>

declare shape{'op}

doc docoff
ml_rw reduce_shape {| reduce |} : ('goal :  shape{'op} ) =
   let op = one_subterm goal in
   let t1 = dest_term (unquote_term op) in
   let bvar_len t = List.length (dest_bterm t).bvars in
      op (* *** BUG *** *)
(*      mk_rlist_term (List.map bvar_len t1.term_terms) *)

doc <:doc<
   @modsubsection{@tt[If_same_op]}

   << if_same_op{'op1; 'op2; 'tt; 'ff} >> evaluates to << 'tt >> if << 'op1 >>
   and << 'op2 >> are two well-formed operators that are the same
   (including all the parameters and all the arities) and to << 'ff >> when
   operators are distinct. Undefined if either << 'op1 >> or << 'op2 >> is
   ill-formed.
>>

declare if_same_op{'op1; 'op2; 'tt; 'ff}

doc docoff
ml_rw reduce_if_same_op {| reduce |} : ('goal :  if_same_op{ 'op1; 'op2; 'tt; 'ff } ) =
   let op1, op2, tt, ff = four_subterms goal in
   let t1 = dest_term (unquote_term op1) in
   let t2 = dest_term (unquote_term op2) in
   let bvar_len t = List.length (dest_bterm t).bvars in
      if    ops_eq t1.term_op t2.term_op
         && List.length t1.term_terms = List.length t2.term_terms
         && List.map bvar_len t1.term_terms = List.map bvar_len t1.term_terms
      then  tt
      else  ff

doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform if_quoted_op_df : if_quoted_op{'op; 'tt} =
   pushm[3] `"if_quoted_op(" slot{'op} `";" space slot{'tt} `")" popm
dform shape_df : shape{'op} =
   `"shape(" slot{'op} `")"
dform if_same_op_df : if_same_op{'op1; 'op2; 'tt; 'ff} =
   szone pushm[3] `"if_same_op(" slot{'op1} `";" hspace slot{'op2} `";" hspace slot{'tt} `";" hspace slot{'ff} `")" popm ezone
