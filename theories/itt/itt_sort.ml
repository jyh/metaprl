(*
 * Define a simple sorting algorithm.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1999 Jason Hickey, Cornell University
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

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError

open Tactic_type
open Tactic_type.Conversionals
open Tactic_type.Tacticals

open Var

open Typeinf
open Base_dtactic

open Itt_rfun
open Itt_list

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*
 * Comparisons.
 *)
define unfold_compare_lt : compare_lt{'lt; 'a; 'b} <-->
   "assert"{('lt 'a 'b)}

(*
 * Type for partial order.
 *)
define unfold_partial_order : partial_order{'A; 'lt} <-->
   ((all a: 'A. not{compare_lt{'lt; 'a; 'a}})
    & (all a: 'A. all b: 'A. all c: 'A. (compare_lt{'lt; 'a; 'b} => compare_lt{'lt; 'b; 'c} => compare_lt{'lt; 'a; 'c})))

(*
 * Definition of a sorted list.
 *)

define unfold_bounded : bounded{'u1; 'l; 'lt} <-->
   list_ind{'l; ."true"; u2, v, g. "and"{."not"{compare_lt{'lt; 'u2; 'u1}}; 'g}}

define unfold_sorted : sorted{'l; 'lt} <-->
   list_ind{'l; ."true"; u, v, g. "and"{bounded{'u; 'v; 'lt}; 'g}}


(*
 * Sorting algorithm.
 *)
define unfold_insert : insert{'u1; 'l; 'lt} <-->
   list_ind{'l; cons{'u1; nil}; u2, v, g.
      ifthenelse{('lt 'u1 'u2); cons{'u1; cons{'u2; 'v}}; cons{'u2; 'g}}}

define unfold_sort : sort{'l; 'lt} <-->
   list_ind{'l; nil; u, v, g. insert{'u; 'g; 'lt}}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

(*
 * Folding.
 *)
let fold_compare_lt = makeFoldC << compare_lt{'lt; 'u; 'v} >> unfold_compare_lt
let fold_bounded = makeFoldC << bounded{'u; 'l; 'lt} >> unfold_bounded
let fold_sorted = makeFoldC << sorted{'l; 'lt} >> unfold_sorted
let fold_insert = makeFoldC << insert{'u; 'l; 'lt} >> unfold_insert
let fold_sort = makeFoldC << sort{'l; 'lt} >> unfold_sort

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

(*
 * Type for partial order.
 *)
dform partial_order_df : except_mode[src] :: partial_order{'A; 'lt} =
   `"PartialOrder(" slot{'lt} " " Nuprl_font!member " " slot{'A} `")"

dform compare_lt_df : except_mode[src] :: compare_lt{'lt; 'a; 'b} =
   `"(" slot{'a} " " `"<[" slot{'lt} `"] " slot{'b} `")"

(*
 * Definition of being sorted.
 *)
dform sorted_df : except_mode[src] :: sorted{'l; 'lt} =
   `"Sorted[" slot{'lt} `"](" slot{'l} `")"

dform bounded_df : except_mode[src] :: bounded{'u; 'l; 'lt} =
   `"(" slot{'u} " " Nuprl_font!le `"[" slot{'lt} `"] " slot{'l} `")"

(*
 * Sorting algorithm.
 *)
dform insert_df : except_mode[src] :: insert{'u; 'l; 'lt} =
   (keyword["insert"] 'u 'l 'lt)

dform sort_df : except_mode[src] :: sort{'l; 'lt} =
   (keyword["sort"] 'l 'lt)

dform list_ind_df : except_mode[src] :: parens :: "prec"[prec_list] :: list_ind{'l; 'base; u, v, g. 'step['g]} =
   szone pushm[0] pushm[1] `"let rec " slot{'g} `" = function" hbreak["",""]
   pushm[5] `"  " cons{'u; 'v} `" ->" hspace slot{'step[('g 'v)]} popm hspace
   pushm[5] `"| [] ->" hspace slot{'base} popm popm hspace
   pushm[3] `"in" hspace slot{'g} `" " slot{'l} popm popm ezone

(************************************************************************
 * REWRITE LEMMAS                                                       *
 ************************************************************************)

interactive_rw reduce_bounded_nil : bounded{'u; nil; 'lt} <--> "true"

interactive_rw reduce_bounded_cons : bounded{'u1; cons{'u2; 'v}; 'lt} <-->
   "and"{."not"{compare_lt{'lt; 'u2; 'u1}}; bounded{'u1; 'v; 'lt}}

interactive_rw reduce_sorted_nil : sorted{nil; 'lt} <--> "true"

interactive_rw reduce_sorted_cons : sorted{cons{'u; 'v}; 'lt} <-->
   "and"{bounded{'u; 'v; 'lt}; sorted{'v; 'lt}}

interactive_rw reduce_insert_nil : insert{'u1; nil; 'lt} <--> cons{'u1; nil}

interactive_rw reduce_insert_cons : insert{'u1; cons{'u2; 'v}; 'lt} <-->
   ifthenelse{('lt 'u1 'u2); cons{'u1; cons{'u2; 'v}}; cons{'u2; insert{'u1; 'v; 'lt}}}

interactive_rw reduce_sort_nil : sort{nil; 'lt} <--> nil

interactive_rw reduce_sort_cons : sort{cons{'u; 'v}; 'lt} <-->
   insert{'u; sort{'v; 'lt}; 'lt}

let resource reduce +=
   [<< bounded{'u; nil; 'lt} >>, reduce_bounded_nil;
    << bounded{'u1; cons{'u2; 'v}; 'lt} >>, reduce_bounded_cons;
    << sorted{nil; 'lt} >>, reduce_sorted_nil;
    << sorted{cons{'u; 'v}; 'lt} >>, reduce_sorted_cons;
    << insert{'u1; nil; 'lt} >>, reduce_insert_nil;
    << insert{'u1; cons{'u2; 'v}; 'lt} >>, reduce_insert_cons;
    << sort{nil; 'lt} >>, reduce_sort_nil;
    << sort{cons{'u; 'v}; 'lt} >>, reduce_sort_cons]

(************************************************************************
 * WELL-FORMEDNESS
 ************************************************************************)

(*
 * Well-formedness of comparisons.
 *)
interactive compare_lt_wf {| intro [intro_typeinf << 'a >>] |} 'H 'A :
   [wf] sequent [squash] { 'H >- 'lt IN 'A -> 'A -> bool } -->
   [wf] sequent [squash] { 'H >- 'a IN 'A } -->
   [wf] sequent [squash] { 'H >- 'b IN 'A } -->
   sequent ['ext] { 'H >- "type" {compare_lt{'lt; 'a; 'b}} }

(*
 * Well-typing of partial_order predicate.
 *)
interactive partial_order_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'lt IN 'A -> 'A -> bool } -->
   sequent ['ext] { 'H >- "type"{partial_order{'A; 'lt}} }

(*
 * Well-formedness of bounded and sorted Boolean functions.
 *)
interactive bounded_wf {| intro [intro_typeinf << 'l >>] |} 'H list{'A} :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'A} } -->
   [wf] sequent [squash] { 'H >- 'u IN 'A } -->
   [wf] sequent [squash] { 'H >- 'lt IN 'A -> 'A -> bool } -->
   sequent ['ext] { 'H >- "type"{bounded{'u; 'l; 'lt}} }

interactive sorted_wf {| intro [intro_typeinf << 'l >>] |} 'H list{'A} :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'A} } -->
   [wf] sequent [squash] { 'H >- 'lt IN 'A -> 'A -> bool } -->
   sequent ['ext] { 'H >- "type"{sorted{'l; 'lt}} }

(*
 * Well formedness of sort and insert functions.
 *)
interactive insert_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'u IN 'A } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'A} } -->
   [wf] sequent [squash] { 'H >- 'lt IN 'A -> 'A -> bool } -->
   sequent ['ext] { 'H >- insert{'u; 'l; 'lt} IN list{'A} }

interactive sort_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'A} } -->
   [wf] sequent [squash] { 'H >- 'lt IN 'A -> 'A -> bool } -->
   sequent ['ext] { 'H >- sort{'l; 'lt} IN list{'A} }

(*
 * Some useful ordering theorems.
 *)
interactive symetric_elim {| elim [elim_typeinf << 'a >>] |} 'H 'J 'A 'v :
   [wf] sequent [squash] { 'H; w: compare_lt{'lt; 'a; 'b}; 'J['w] >- 'lt IN 'A -> 'A -> bool } -->
   [wf] sequent [squash] { 'H; w: compare_lt{'lt; 'a; 'b}; 'J['w] >- 'a IN 'A } -->
   [wf] sequent [squash] { 'H; w: compare_lt{'lt; 'a; 'b}; 'J['w] >- 'b IN 'A } -->
   [main] sequent ['ext] { 'H; w: compare_lt{'lt; 'a; 'b}; 'J['w] >- partial_order{'A; 'lt} } -->
   [main] sequent ['ext] { 'H; w: compare_lt{'lt; 'a; 'b}; 'J['w]; v: not{compare_lt{'lt; 'b; 'a}} >- 'C['w] } -->
   sequent ['ext] { 'H; w: (compare_lt{'lt; 'a; 'b}); 'J['w] >- 'C['w] }

interactive bounded_inclusion 'H list{'A} 'u1 :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'u IN 'A } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'A} } -->
   [wf] sequent [squash] { 'H >- 'lt IN 'A -> 'A -> bool } -->
   [wf] sequent [squash] { 'H >- 'u1 IN 'A } -->
   [main] sequent ['ext] { 'H >- partial_order{'A; 'lt} } -->
   [main] sequent ['ext] { 'H >- compare_lt{'lt; 'u; 'u1} } -->
   [main] sequent ['ext] { 'H >- bounded{'u1; 'l; 'lt} } -->
   sequent ['ext] { 'H >- bounded{'u; 'l; 'lt} }

let boundInclusionT t p =
   let goal = Sequent.concl p in
   let _, l, _ =
      try three_subterms goal with
         RefineError _ ->
            raise (RefineError("boundInclusion", StringTermError("not a \"bounded\" term",goal)))
   in
   let a_type =
      try get_with_arg p with
         RefineError _ ->
            begin try infer_type p l with
               RefineError _ ->
                  raise (RefineError("boundInclusion", StringTermError("can not infer type",l)))
            end
   in
      bounded_inclusion (Sequent.hyp_count_addr p) a_type t p

interactive insert_inclusion 'H 'A :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'u IN 'A } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'A} } -->
   [wf] sequent [squash] { 'H >- 'lt IN 'A -> 'A -> bool } -->
   [wf] sequent [squash] { 'H >- 'u1 IN 'A } -->
   [main] sequent ['ext] { 'H >- partial_order{'A; 'lt} } -->
   [main] sequent ['ext] { 'H >- not{compare_lt{'lt; 'u1; 'u}} } -->
   [main] sequent ['ext] { 'H >- bounded{'u; 'l; 'lt} } -->
   sequent ['ext] { 'H >- bounded{'u; insert{'u1; 'l; 'lt}; 'lt} }

let insertInclusionT p =
   let goal = Sequent.concl p in
   let u, _, _ = three_subterms goal in
   let a_type =
      try get_with_arg p with
         RefineError _ ->
            infer_type p u
   in
      insert_inclusion (Sequent.hyp_count_addr p) a_type p

(*
 * Properties of insert
 *)
interactive insert_mem {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'A} } -->
   [wf] sequent [squash] { 'H >- 'u IN 'A } -->
   [wf] sequent [squash] { 'H >- 'lt IN 'A -> 'A -> bool } -->
   [wf] sequent ['ext] { 'H >- partial_order{'A; 'lt} } -->
   sequent ['ext] { 'H >- mem{'u; insert{'u; 'l; 'lt}; 'A} }

interactive insert_subset {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'u IN 'A } -->
   [wf] sequent [squash] { 'H >- 'v IN list{'A} } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'A} } -->
   [wf] sequent [squash] { 'H >- 'lt IN 'A -> 'A -> bool } -->
   [wf] sequent ['ext] { 'H >- partial_order{'A; 'lt} } -->
   sequent ['ext] { 'H >- subset{'v; 'l; 'A} } -->
   sequent ['ext] { 'H >- subset{'v; insert{'u; 'l; 'lt}; 'A} }

interactive subset_insert_cons {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'u IN 'A } -->
   [wf] sequent [squash] { 'H >- 'v IN list{'A} } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'A} } -->
   [wf] sequent [squash] { 'H >- 'lt IN 'A -> 'A -> bool } -->
   [wf] sequent ['ext] { 'H >- partial_order{'A; 'lt} } -->
   sequent ['ext] { 'H >- subset{'v; 'l; 'A} } -->
   sequent ['ext] { 'H >- subset{insert{'u; 'v; 'lt}; cons{'u; 'l}; 'A} }

(*
 * Verifications of the functions.
 *)
interactive insert_thm {| intro [intro_typeinf << 'l >>] |} 'H list{'A} :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'A} } -->
   [wf] sequent [squash] { 'H >- 'u IN 'A } -->
   [wf] sequent [squash] { 'H >- 'lt IN 'A -> 'A -> bool } -->
   [wf] sequent ['ext] { 'H >- partial_order{'A; 'lt} } -->
   [main] sequent ['ext] { 'H >- sorted{'l; 'lt} } -->
   sequent ['ext] { 'H >- sorted{insert{'u; 'l; 'lt}; 'lt} }

interactive sorted_thm {| intro [intro_typeinf << 'l >>] |} 'H list{'A} :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'A} } -->
   [wf] sequent [squash] { 'H >- 'lt IN 'A -> 'A -> bool } -->
   [wf] sequent ['ext] { 'H >- partial_order{'A; 'lt} } -->
   sequent ['ext] { 'H >- sorted{sort{'l; 'lt}; 'lt} }

interactive sort_sameset {| intro [intro_typeinf << 'l >>] |} 'H list{'A} :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'A} } -->
   [wf] sequent [squash] { 'H >- 'lt IN 'A -> 'A -> bool } -->
   [wf] sequent ['ext] { 'H >- partial_order{'A; 'lt} } -->
   sequent ['ext] { 'H >- sameset{sort{'l; 'lt}; 'l; 'A} }

(*
 * -*-
 * LOCAL Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
