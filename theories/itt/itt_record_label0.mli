(* Labels as natural numberas *)

include Itt_nat

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


declare undefined{}
define unfoldInd :   ind_lab{'n; 'base; l. 'up['l]} <-->
                     ind{'n; i,j.undefined; 'base; k,l . 'up['l]}


declare eq_label{'x;'y}

rule decide_eq_label 'H 'x 'y :
   [wf] sequent[squash] {'H >- 'x IN label} -->
   [wf] sequent[squash] {'H >- 'y IN label} -->
   sequent['ext] {'H; u:'x='y in label >- 'C} -->
   sequent['ext] {'H; u:not{.'x='y in label} >- 'C} -->
   sequent['ext] {'H >- 'C}

topval reduce_eq_label_true_rw : conv
topval reduce_eq_label_false_rw : conv

topval decideEqLabelT : term -> term -> tactic
