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
extends Base_meta
doc docoff

open Basic_tactics
open Base_meta

open Lm_debug
open Lm_symbol
open Lm_printf
open Lm_rformat

open Dform

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

doc <:doc<
   @modsection{Computational Operations on Operators}
   @modsubsection{@tt[Shape]}

   << shape[op:op] >> is a list of natural numbers that are meant to represent
   the number of bindings in each of the operator's arguments. The length of
   the list is the operator's arity.
>>

declare shape[op:op]

doc docoff

ml_rw reduce_shape {| reduce |} : ('goal :  shape[op:op] ) =
   match dest_params (dest_op (dest_term goal).term_op).op_params with
      [ Operator op ] ->
         mk_rlist_term (List.map mk_meta_num op.opparam_arities)
    | _ ->
         raise (RefineForceError("Base_operator.reduce_shape", "Internal error", TermError goal))

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform shape_df : shape[op:op] =
   `"shape(" slot[op:op] `")"
