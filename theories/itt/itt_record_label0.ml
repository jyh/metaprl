(* labels as natural numberas *)

include Itt_nat
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


let rwaAll convs = onAllMClausesT (rwa convs)

let rwAll c = onAllMClausesT (rw c)

let rwhAll c = onAllMClausesT (rwh c)


(******************)
(*  Defenitions   *)
(******************)


define unfold_label : label <--> nat


define unfold_zero : zero <--> 0


define unfold_next : next{'x} <--> ('x +@ 1)


declare undefined{}
define unfoldInd :   ind_lab{'n; 'base; l. 'up['l]} <-->
                     ind{'n; i,j.undefined; 'base; k,l . 'up['l]}


define unfold_eq_label : eq_label{'x;'y} <--> eq_int{'x;'y}

(******************)
(*   Rules        *)
(******************)

interactive labelType {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- "type"{label} }

interactive zeroMember {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- zero IN label}

interactive nextMember {| intro_resource [] |} 'H :
   sequent [squash] { 'H >- 'x='y in label} -->
   sequent ['ext] { 'H >- next{'x} = next{'y} in label}

interactive labelInduction {| elim_resource [ThinOption thinT] |} 'H 'J 'n 'm 'z :
   sequent ['ext] { 'H; n: label; 'J['n] >- 'C[zero] }  -->
   sequent ['ext] { 'H; n: label; 'J['n]; m: label;  z: 'C['m] >- 'C[next{'m}] }  -->
   sequent ['ext] { 'H; n: label; 'J['n] >- 'C['n] }

interactive labelBackInduction 'H 'n bind{x.'C['x]} 'm 'z :
   sequent [squash]{'H >- 'n IN label }  -->
   sequent ['ext] { 'H >- 'C['n] }  -->
   sequent ['ext] { 'H; m: label;  z: 'C[next{'m}] >- 'C['m] }  -->
   sequent ['ext] { 'H  >- 'C[zero] }


(**** ind ****)

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

(**** equality ****)

interactive label_sqequal 'H:
   sequent[squash] {'H >-'n = 'm  in label} -->
   sequent['ext] {'H >- 'n ~ 'm}

interactive reduce_eq_label_true {| intro_resource [] |} 'H:
   sequent[squash] {'H >-'n = 'm  in label} -->
   sequent['ext] {'H >- eq_label{'n;'m} ~ btrue}

interactive reduce_eq_label_false {| intro_resource [] |} 'H:
   sequent[squash] {'H >- not{.'n = 'm  in label}} -->
   sequent['ext] {'H >- eq_label{'n;'m} ~ bfalse}

interactive_rw reduce_eq_label_true_rw :
   ('n = 'm  in label) -->
   eq_label{'n;'m} <--> btrue

interactive_rw reduce_eq_label_false_rw :
   (not{.'n = 'm  in label}) -->
   eq_label{'n;'m} <--> bfalse

interactive decide_eq_label 'H 'x 'y :
   [wf] sequent[squash] {'H >- 'x IN label} -->
   [wf] sequent[squash] {'H >- 'y IN label} -->
   [main] sequent['ext] {'H; u:'x='y in label >- 'C} -->
   [main] sequent['ext] {'H; u:not{.'x='y in label} >- 'C} -->
   sequent['ext] {'H >- 'C}

(******************)
(*   Tactic       *)
(******************)


let decideEqLabelT x y =
   let tac p =
      decide_eq_label (Sequent.hyp_count_addr p) x y p
   in
      tac thenLT [idT;
                  idT;
                  tryT (rwhAll reduce_eq_label_true_rw
                        thenAT nthHypT (-1)
                        thenT rwhAll reduce_ifthenelse_true);
                  tryT (rwhAll reduce_eq_label_false_rw
                        thenAT nthHypT (-1)
                        thenT rwhAll reduce_ifthenelse_false)
                 ]




(******************)
(*  Display Forms *)
(******************)

dform label_df : except_mode [src] :: label = `"Label"

dform zero_df : except_mode [src] :: zero = `"0"

dform next_df : except_mode [src] :: next{'x} = slot{'x}  `"'"

dform eq_label_df : except_mode[src] :: eq_label{'x;'y} =   slot{'x} space `"=" space slot{'y}
