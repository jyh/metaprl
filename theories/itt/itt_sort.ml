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

include Itt_theory

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

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*
 * Type for partial order.
 *)
declare partial_order{'A; 'lt}
declare compare_lt{'lt; 'a; 'b}

(*
 * Definition of being sorted.
 *)
declare sorted{'l; 'lt}
declare bounded{'u; 'l; 'lt}

(*
 * Sorting algorithm.
 *)
declare insert{'u; 'l; 'lt}
declare sort{'l; 'lt}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

(*
 * Comparisons.
 *)
prim_rw unfold_compare_lt : compare_lt{'lt; 'a; 'b} <-->
   ('lt 'a 'b)

(*
 * Definition of partial order.
 *)
prim_rw unfold_partial_order : partial_order{'A; 'lt} <-->
   ((all a: 'A. "assert"{bnot{compare_lt{'lt; 'a; 'a}}})
    & (all a: 'A. all b: 'A. ("assert"{compare_lt{'lt; 'a; 'b}} => "assert"{bnot{compare_lt{'lt; 'b; 'a}}}))
    & (all a: 'A. all b: 'A. all c: 'A. ("assert"{compare_lt{'lt; 'a; 'b}} => "assert"{compare_lt{'lt; 'b; 'c}} => "assert"{compare_lt{'lt; 'a; 'c}})))

(*
 * Definition of a sorted list.
 *)
prim_rw unfold_bounded : bounded{'u1; 'l; 'lt} <-->
   list_ind{'l; ."btrue"; u2, v, g. band{bnot{compare_lt{'lt; 'u2; 'u1}}; 'g}}

prim_rw unfold_sorted : sorted{'l; 'lt} <-->
   list_ind{'l; ."btrue"; u, v, g. band{bounded{'u; 'v; 'lt}; 'g}}

(*
 * Define it.
 *)
prim_rw unfold_insert : insert{'u1; 'l; 'lt} <-->
   list_ind{'l; cons{'u1; nil}; u2, v, g.
      ifthenelse{compare_lt{'lt; 'u1; 'u2}; cons{'u1; cons{'u2; 'v}}; cons{'u2; 'g}}}

prim_rw unfold_sort : sort{'l; 'lt} <-->
   list_ind{'l; nil; u, v, g. insert{'u; 'g; 'lt}}

(*
 * Folding.
 *)
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
dform partial_order_df : partial_order{'A; 'lt} =
   `"PartialOrder(" slot{'lt} " " Nuprl_font!member " " slot{'A} `")"

dform compare_lt_df : compare_lt{'lt; 'a; 'b} =
   ('lt 'a 'b)

(*
 * Definition of being sorted.
 *)
dform sorted_df : sorted{'l; 'lt} =
   `"Sorted[" slot{'lt} `"](" slot{'l} `")"

dform bounded_df : bounded{'u; 'l; 'lt} =
   `"(" slot{'u} " " Nuprl_font!le `"[" slot{'lt} `"] " slot{'l} `")"

(*
 * Sorting algorithm.
 *)
dform insert_df : insert{'u; 'l; 'lt} =
   (keyword["insert"] 'u 'l 'lt)

dform sort_df : sort{'l; 'lt} =
   (keyword["sort"] 'l 'lt)

dform list_ind_df : list_ind{'l; 'base; u, v, g. 'step} =
   szone pushm[0] pushm[1] `"let rec " slot{'g} `"_fun = function" break["",""]
   pushm[5] `"  " cons{'u; 'v} `" ->" hspace
      szone `"let " slot{'g} `" = " slot{'g} `"_fun " slot{'v} `" in" hspace slot{'step} ezone popm hspace
   pushm[5] `"| [] ->" hspace slot{'base} popm popm hspace
   pushm[3] `"in" hspace slot{'g} `"_fun " slot{'l} popm popm ezone

(************************************************************************
 * REWRITE LEMMAS                                                       *
 ************************************************************************)

interactive_rw reduce_bounded_nil : bounded{'u; nil; 'lt} <--> btrue

interactive_rw reduce_bounded_cons : bounded{'u1; cons{'u2; 'v}; 'lt} <-->
   band{bnot{compare_lt{'lt; 'u2; 'u1}}; bounded{'u1; 'v; 'lt}}

interactive_rw reduce_sorted_nil : sorted{nil; 'lt} <--> btrue

interactive_rw reduce_sorted_cons : sorted{cons{'u; 'v}; 'lt} <-->
   band{bounded{'u; 'v; 'lt}; sorted{'v; 'lt}}

interactive_rw reduce_insert_nil : insert{'u1; nil; 'lt} <--> cons{'u1; nil}

interactive_rw reduce_insert_cons : insert{'u1; cons{'u2; 'v}; 'lt} <-->
   ifthenelse{compare_lt{'lt; 'u1; 'u2}; cons{'u1; cons{'u2; 'v}}; cons{'u2; insert{'u1; 'v; 'lt}}}

interactive_rw reduce_sort_nil : sort{nil; 'lt} <--> nil

interactive_rw reduce_sort_cons : sort{cons{'u; 'v}; 'lt} <-->
   insert{'u; sort{'v; 'lt}; 'lt}

let reduce_info =
   [<< bounded{'u; nil; 'lt} >>, reduce_bounded_nil;
    << bounded{'u1; cons{'u2; 'v}; 'lt} >>, reduce_bounded_cons;
    << sorted{nil; 'lt} >>, reduce_sorted_nil;
    << sorted{cons{'u; 'v}; 'lt} >>, reduce_sorted_cons;
    << insert{'u1; nil; 'lt} >>, reduce_insert_nil;
    << insert{'u1; cons{'u2; 'v}; 'lt} >>, reduce_insert_cons;
    << sort{nil; 'lt} >>, reduce_sort_nil;
    << sort{cons{'u; 'v}; 'lt} >>, reduce_sort_cons]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info

(************************************************************************
 * WELL-FORMEDNESS
 ************************************************************************)

(*
 * Well-formedness of comparisons.
 *)
interactive compare_lt_wf {| intro_resource [IntroArgsOption (infer_type_args, Some << 'a >>)] |} 'H 'A :
   [wf] sequent [squash] { 'H >- member{.'A -> 'A -> bool; 'lt} } -->
   [wf] sequent [squash] { 'H >- member{'A; 'a} } -->
   [wf] sequent [squash] { 'H >- member{'A; 'b} } -->
   sequent ['ext] { 'H >- member{bool; compare_lt{'lt; 'a; 'b}} }

(*
 * Well-typing of partial_order predicate.
 *)
interactive partial_order_wf {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- member{.'A -> 'A -> bool; 'lt} } -->
   sequent ['ext] { 'H >- "type"{partial_order{'A; 'lt}} }

(*
 * Well-formedness of bounded and sorted Boolean functions.
 *)
interactive bounded_wf {| intro_resource [IntroArgsOption (infer_type_args, Some << 'l >>)] |} 'H list{'A} :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- member{list{'A}; 'l} } -->
   [wf] sequent [squash] { 'H >- member{'A; 'u} } -->
   [wf] sequent [squash] { 'H >- member{.'A -> 'A -> bool; 'lt} } -->
   sequent ['ext] { 'H >- member{bool; bounded{'u; 'l; 'lt}} }

interactive sorted_wf {| intro_resource [IntroArgsOption (infer_type_args, Some << 'l >>)] |} 'H list{'A} :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- member{list{'A}; 'l} } -->
   [wf] sequent [squash] { 'H >- member{.'A -> 'A -> bool; 'lt} } -->
   sequent ['ext] { 'H >- member{bool; sorted{'l; 'lt}} }

(*
 * Well formedness of sort and insert functions.
 *)
interactive insert_wf {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- member{'A; 'u} } -->
   [wf] sequent [squash] { 'H >- member{list{'A}; 'l} } -->
   [wf] sequent [squash] { 'H >- member{.'A -> 'A -> bool; 'lt} } -->
   sequent ['ext] { 'H >- member{list{'A}; insert{'u; 'l; 'lt}} }

interactive sort_wf {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- member{list{'A}; 'l} } -->
   [wf] sequent [squash] { 'H >- member{.'A -> 'A -> bool; 'lt} } -->
   sequent ['ext] { 'H >- member{list{'A}; sort{'l; 'lt}} }

(*
 * Some useful ordering theorems.
 *)
interactive symetric_elim {| elim_resource [ElimArgsOption (infer_type_args, Some << 'a >>)] |} 'H 'J 'A 'v :
   [wf] sequent [squash] { 'H; w: "assert"{compare_lt{'lt; 'a; 'b}}; 'J['w] >- member{.'A -> 'A -> bool; 'lt} } -->
   [wf] sequent [squash] { 'H; w: "assert"{compare_lt{'lt; 'a; 'b}}; 'J['w] >- member{'A; 'a} } -->
   [wf] sequent [squash] { 'H; w: "assert"{compare_lt{'lt; 'a; 'b}}; 'J['w] >- member{'A; 'b} } -->
   [main] sequent ['ext] { 'H; w: "assert"{compare_lt{'lt; 'a; 'b}}; 'J['w] >- partial_order{'A; 'lt} } -->
   [main] sequent ['ext] { 'H; w: "assert"{compare_lt{'lt; 'a; 'b}}; 'J['w]; v: "assert"{bnot{compare_lt{'lt; 'b; 'a}}} >- 'C['w] } -->
   sequent ['ext] { 'H; w: ("assert"{compare_lt{'lt; 'a; 'b}}); 'J['w] >- 'C['w] }

interactive bounded_inclusion 'H list{'A} 'u1 :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- member{'A; 'u} } -->
   [wf] sequent [squash] { 'H >- member{list{'A}; 'l} } -->
   [wf] sequent [squash] { 'H >- member{.'A -> 'A -> bool; 'lt} } -->
   [wf] sequent [squash] { 'H >- member{'A; 'u1} } -->
   [main] sequent ['ext] { 'H >- partial_order{'A; 'lt} } -->
   [main] sequent [squash] { 'H >- "assert"{compare_lt{'lt; 'u; 'u1}} } -->
   [main] sequent [squash] { 'H >- "assert"{bounded{'u1; 'l; 'lt}} } -->
   sequent ['ext] { 'H >- "assert"{bounded{'u; 'l; 'lt}} }

let boundInclusionT t p =
   let goal = Sequent.concl p in
   let _, l, _ = three_subterms (one_subterm goal) in
   let a_type =
      try get_with_arg p with
         RefineError _ ->
            snd (infer_type p l)
   in
      bounded_inclusion (Sequent.hyp_count_addr p) a_type t p

interactive insert_inclusion 'H 'A :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- member{'A; 'u} } -->
   [wf] sequent [squash] { 'H >- member{list{'A}; 'l} } -->
   [wf] sequent [squash] { 'H >- member{.'A -> 'A -> bool; 'lt} } -->
   [wf] sequent [squash] { 'H >- member{'A; 'u1} } -->
   [main] sequent ['ext] { 'H >- partial_order{'A; 'lt} } -->
   [main] sequent [squash] { 'H >- "assert"{bnot{compare_lt{'lt; 'u1; 'u}}} } -->
   [main] sequent [squash] { 'H >- "assert"{bounded{'u; 'l; 'lt}} } -->
   sequent ['ext] { 'H >- "assert"{bounded{'u; insert{'u1; 'l; 'lt}; 'lt}} }

let insertInclusionT p =
   let goal = Sequent.concl p in
   let u, _, _ = three_subterms (one_subterm goal) in
   let a_type =
      try get_with_arg p with
         RefineError _ ->
            snd (infer_type p u)
   in
      insert_inclusion (Sequent.hyp_count_addr p) a_type p

(*
 * Verifications of the functions.
 *)
interactive insert_thm {| intro_resource [IntroArgsOption (infer_type_args, Some << 'l >>)] |} 'H list{'A} :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- member{list{'A}; 'l} } -->
   [wf] sequent [squash] { 'H >- member{'A; 'u} } -->
   [wf] sequent [squash] { 'H >- member{.'A -> 'A -> bool; 'lt} } -->
   [wf] sequent [squash] { 'H >- partial_order{'A; 'lt} } -->
   [main] sequent ['ext] { 'H >- "assert"{sorted{'l; 'lt}} } -->
   sequent ['ext] { 'H >- "assert"{sorted{insert{'u; 'l; 'lt}; 'lt}} }

interactive sorted_thm {| intro_resource [IntroArgsOption (infer_type_args, Some << 'l >>)] |} 'H list{'A} :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- member{list{'A}; 'l} } -->
   [wf] sequent [squash] { 'H >- member{.'A -> 'A -> bool; 'lt} } -->
   [wf] sequent [squash] { 'H >- partial_order{'A; 'lt} } -->
   sequent ['ext] { 'H >- "assert"{sorted{sort{'l; 'lt}; 'lt}} }

(*
 * -*-
 * LOCAL Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
