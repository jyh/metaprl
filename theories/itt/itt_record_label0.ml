(* labels as natural numberas *)

include Itt_nat
include Itt_struct2
include Itt_struct3

open Base_meta
open Itt_int_ext
open Itt_struct
open Itt_struct3
open Base_dtactic
open Tactic_type.Conversionals
open Var
open Tactic_type
open Tactic_type.Tacticals
open Itt_bool
open Itt_struct2

(*
let rwAll c = onAllMClausesT (rw c)

let rwaAll convs = onAllMClausesT (rwa convs)

let rwhAll c = onAllMClausesT (rwh c)
*)

(******************)
(*  Defenitions   *)
(******************)


define unfold_label : label <--> nat


define unfold_zero : zero <--> 0


define unfold_next : next{'x} <--> ('x +@ 1)


define unfoldInd :   ind_lab{'n; 'base; l. 'up['l]} <-->
                     ind{'n; 'base; k,l . 'up['l]}



interactive_rw reduce_ind_up :
   ('x IN label) -->
   ind_lab{next{'x}; 'base; l. 'up['l]} <-->
   ('up[ind_lab{'x ; 'base; l. 'up['l]}])

interactive_rw reduce_ind_base :
   (ind_lab{zero; 'base; l. 'up['l]}) <-->
   'base

(*! @docoff *)
let resource reduce +=
   [<< ind_lab{next{'x}; 'base; l. 'up['l]} >>, reduce_ind_up;
    << ind_lab{zero; 'base; l. 'up['l]} >>, reduce_ind_base]


(******************)
(*   Rules        *)
(******************)

interactive labelType {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{label} }

interactive zeroMember {| intro [] |} 'H :
   sequent ['ext] { 'H >- zero IN label}

interactive nextMember {| intro [] |} 'H :
   sequent [squash] { 'H >- 'x='y in label} -->
   sequent ['ext] { 'H >- next{'x} = next{'y} in label}

interactive labelInduction {| elim [ThinOption thinT] |} 'H 'J 'n 'm 'z :
   sequent ['ext] { 'H; n: label; 'J['n] >- 'C[zero] }  -->
   sequent ['ext] { 'H; n: label; 'J['n]; m: label;  z: 'C['m] >- 'C[next{'m}] }  -->
   sequent ['ext] { 'H; n: label; 'J['n] >- 'C['n] }

interactive labelBackInduction 'H 'n bind{x.'C['x]} 'm 'z :
   sequent [squash]{'H >- 'n IN label }  -->
   sequent ['ext] { 'H >- 'C['n] }  -->
   sequent ['ext] { 'H; m: label;  z: 'C[next{'m}] >- 'C['m] }  -->
   sequent ['ext] { 'H  >- 'C[zero] }



(**** equality ****)

interactive label_sqequal 'H:
   sequent[squash] {'H >-'n = 'm  in label} -->
   sequent['ext] {'H >- 'n ~ 'm}

interactive decide_eq_label 'H 'x 'y :
   [wf] sequent[squash] {'H >- 'x IN label} -->
   [wf] sequent[squash] {'H >- 'y IN label} -->
   [main] sequent['ext] {'H; u:'x='y in label >- 'C} -->
   [main] sequent['ext] {'H; u:not{.'x='y in label} >- 'C} -->
   sequent['ext] {'H >- 'C}

(******************)
(*   Tactic       *)
(******************)



(******************)
(*  Display Forms *)
(******************)

dform label_df : except_mode [src] :: label = `"Label"

dform zero_df : except_mode [src] :: zero = `"0"

dform next_df : except_mode [src] :: next{'x} = slot{'x}  `"'"

