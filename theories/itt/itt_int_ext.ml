include Itt_equal
include Itt_rfun
include Itt_logic
include Itt_bool
include Itt_int_base

open Printf
open Mp_debug
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Rformat
open Mp_resource

open Var
open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Base_meta
open Base_dtactic

open Itt_equal
open Itt_struct
(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "mul"{'a; 'b}
declare "div"{'a; 'b}
declare "rem"{'a; 'b}

prim mul_wf 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   [wf] sequent [squash] { 'H >- 'b = 'b1 in int } -->
   sequent ['ext] { 'H >- 'a *@ 'b = 'a1 *@ 'b1 in int } = it

(*
 Definitions of >b <=b >=b
 *)

declare gt_bool{'a; 'b}

declare le_bool{'a; 'b}

declare ge_bool{'a; 'b}

prim_rw unfold_gt_bool :
   gt_bool{'a; 'b} <--> lt_bool{'b; 'a}

prim_rw unfold_le_bool :
   le_bool{'a; 'b} <--> bnot{lt_bool{'b; 'a}}

prim_rw unfold_ge_bool :
   ge_bool{'a; 'b} <--> bnot{lt_bool{'a; 'b}}

declare bneq_int{'a; 'b}

prim_rw unfold_bneq_int :
   bneq_int{'a; 'b} <--> bnot{beq_int{'a; 'b}}

(*
 Prop-int-relations definitions
 *)

declare gt{'a; 'b}

prim_rw unfold_lt :
   lt{'a; 'b} <--> "assert"{lt_bool{'a; 'b}}

prim_rw unfold_gt :
   gt{'a; 'b} <--> ('b < 'a)

(*
Switching to define-version to provide the same behaviour as bool-relations,
i.d. rewritability of <= in the same extent as of <

prim_rw unfold_le 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- 'a <= 'b <--> ('a < 'b) \/ ('a = 'b in int) }

prim_rw unfold_ge 'H :
   [wf] sequent [squash] { 'H >- a IN int } -->
   [wf] sequent [squash] { 'H >- b IN int } -->
   sequent ['ext] { 'H >- 'a >= 'b <--> ('a < 'b) \/ ('a = 'b in int) }
*)

declare le{'a; 'b}

declare ge{'a; 'b}

declare nequal{'a; 'b}

prim_rw unfold_le :
   le{'a; 'b} <--> "assert"{le_bool{'a; 'b}}

prim_rw unfold_ge :
   ge{'a; 'b} <--> ('b <= 'a)

prim_rw unfold_neq_int :
   nequal{'a; 'b} <--> "assert"{bneq_int{'a; 'b}}

nteractive_rw lt_mulPositMono 'H 'c:
   (0 < 'c ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   lt_bool{'a; 'b} <--> lt_bool{('c *@ 'a); ('c *@ 'b) }

prim_rw mul_Commut 'H :
   ('a IN int ) -->
   ('b IN int ) -->
   ('a *@ 'b) <--> ('b *@ 'a)

prim_rw mul_Assoc 'H :
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ('a *@ ('b *@ 'c)) <--> (('a *@ 'b) *@ 'c) 

prim_rw mul_add_Distrib 'H :
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ('a *@ ('b +@ 'c)) <--> (('a *@ 'b) +@ ('a *@ 'c)) 

prim_rw mul_Id 'H :
   ('a IN int ) -->
   'a <--> (1 *@ 'a) 

prim_rw mul_Zero 'H :
   ('a IN int ) -->
   (0 *@ 'a) <--> 0
 
interactive_rw mul_uni_Assoc 'H :
   ('a IN int ) -->
   ('b IN int ) -->
   ('a *@ uni_minus{ 'b }) <--> (uni_minus{ 'a } *@ 'b)

interactive_rw lt_mulNegMono 'H 'c:
   ('c < 0 ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   lt_bool{'a; 'b} <--> lt_bool{('c *@ 'b) ; ('c *@ 'a)} 

prim_rw rem_baseReduce 'H:
   (0 <= 'a ) -->
   ('a < 'b ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('a rem 'b) <--> 'a 

prim_rw rem_indReduce 'H:
   (0 < 'b ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ((('a *@ 'b) +@ 'c) rem 'b) <--> ('c rem 'b) 

interactive rem_wf 'H :
   sequent [squash] { 'H >- "nequal"{'b ; 0} } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- ('a rem 'b) IN int }

prim_rw div_baseReduce 'H:
   (0 <= 'a ) -->
   ('a < 'b ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('a /@ 'b) <--> 0

prim_rw div_indReduce 'H:
   (0 < 'b ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ((('a *@ 'b) +@ 'c) /@ 'b) <--> ('a +@ ('c /@ 'b)) 

interactive div_wf 'H :
   sequent [squash] { 'H >- "nequal"{'b ; 0} } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- 'a /@ 'b IN int }

interactive lt_divMono 'H 'b :
   sequent [squash] { 'H >- 0 < 'c } -->
   sequent [squash] { 'H >- 'a < 'b } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- 'a /@ 'c <= 'b /@ 'c }

interactive add_divReduce 'H:
   sequent [squash] {'H >- 0 < 'a } -->
   sequent [squash] {'H >- 0 < 'b } -->
   sequent [squash] {'H >- 0 < 'c } -->
   [wf] sequent [squash] {'H >- 'a IN int } -->
   [wf] sequent [squash] {'H >- 'b IN int } -->
   [wf] sequent [squash] {'H >- 'c IN int } -->
   sequent ['ext] {'H >- ('a /@ 'c) +@ ('b /@ 'c) <= ('a +@ 'b) /@ 'c }

interactive_rw div_Assoc 'H:
   (0 <= 'a ) -->
   (0 < 'b ) -->
   (0 < 'c ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   (('a /@ 'b) /@ 'c) <--> ('a /@ ('b *@ 'c))

(*
Incorrect but there has to be some assoc/commut/composition property

rewrite rem_Assoc 'H:
   sequent [squash] { 'H >- 0 <= 'a } -->
   sequent [squash] { 'H >- 0 < 'b } -->
   sequent [squash] { 'H >- 0 < 'c } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- ('a rem 'b) rem 'c <--> ('a rem 'c) rem 'b }

*)


