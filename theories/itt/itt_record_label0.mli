(* Labels as natural numberas *)

extends Itt_nat

open Refiner.Refiner.Term
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals

(*
topval rwaAll  :  conv list -> tactic

topval rwAll  :  conv -> tactic

topval rwhAll  :  conv -> tactic
*)

define unfold_label : label <--> nat


define unfold_zero : zero <--> 0


define unfold_next : next{'x} <--> ('x +@ 1)

define unfoldInd :   ind_lab{'n; 'base; l. 'up['l]} <-->
                     ind{'n; 'base; k,l . 'up['l]}


rule decide_eq_label 'x 'y :
   [wf] sequent{ <H> >- 'x in label} -->
   [wf] sequent{ <H> >- 'y in label} -->
   sequent{ <H>; u:'x='y in label >- 'C} -->
   sequent{ <H>; u:not{.'x='y in label} >- 'C} -->
   sequent{ <H> >- 'C}

