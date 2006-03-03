(* labels as natural numberas *)

extends Itt_nat
extends Itt_struct2
extends Itt_struct3
extends Itt_nequal

open Basic_tactics
open Itt_struct

(******************)
(*  Defenitions   *)
(******************)

define unfold_label : label <--> nat

define unfold_zero : zero <--> 0

define unfold_next : next{'x} <--> ('x +@ 1)

define unfoldInd :   ind_lab{'n; 'base; l. 'up['l]} <-->
                     ind{'n; 'base; k,l . 'up['l]}

interactive_rw reduce_ind_up {| reduce |} :
   ('x in label) -->
   ind_lab{next{'x}; 'base; l. 'up['l]} <-->
   ('up[ind_lab{'x ; 'base; l. 'up['l]}])

interactive_rw reduce_ind_base {| reduce |} :
   (ind_lab{zero; 'base; l. 'up['l]}) <-->
   'base

(******************)
(*   Rules        *)
(******************)

interactive labelType {| intro [] |} :
   sequent { <H> >- "type"{label} }

interactive labelType_univ {| intro [] |} :
   sequent { <H> >- label in univ[i:l] }

interactive zeroMember {| intro [] |} :
   sequent { <H> >- zero in label}

interactive nextMember {| intro [] |} :
   sequent { <H> >- 'x='y in label} -->
   sequent { <H> >- next{'x} = next{'y} in label}

interactive labelInduction {| elim [ThinOption thinT] |} 'H :
   sequent { <H>; n: label; <J['n]> >- 'C[zero] }  -->
   sequent { <H>; n: label; <J['n]>; m: label;  z: 'C['m] >- 'C[next{'m}] }  -->
   sequent { <H>; n: label; <J['n]> >- 'C['n] }

interactive labelBackInduction 'n bind{x.'C['x]} :
   sequent { <H> >- 'n in label }  -->
   sequent { <H> >- 'C['n] }  -->
   sequent { <H>; m: label;  z: 'C[next{'m}] >- 'C['m] }  -->
   sequent { <H>  >- 'C[zero] }

(**** equality ****)

interactive label_sqequal {| nth_hyp |} :
   sequent{ <H> >-'n = 'm  in label} -->
   sequent{ <H> >- 'n ~ 'm}

interactive decide_eq_label 'x 'y :
   [wf] sequent{ <H> >- 'x in label} -->
   [wf] sequent{ <H> >- 'y in label} -->
   [main] sequent{ <H>; u: 'x='y in label >- 'C} -->
   [main] sequent{ <H>; u: 'x<>'y in label >- 'C} -->
   sequent{ <H> >- 'C}

interactive decide_eq_label2 'x 'y :
   [wf] sequent{ <H> >- 'x in label} -->
   [wf] sequent{ <H> >- 'y in label} -->
   [main] sequent{ <H>; u:'x~'y >- 'C} -->
   [main] sequent{ <H>; u: 'x<>'y in label >- 'C} -->
   sequent{ <H> >- 'C}

let decideEqLabel0T x y = decide_eq_label2 x y thenLT [idT;idT; hypSubstT (-1) 0; idT]

doc docoff

(******************)
(*   Tactic       *)
(******************)

(******************)
(*  Display Forms *)
(******************)

dform label_df : except_mode [src] :: label = `"Label"

dform zero_df : except_mode [src] :: zero = `"0"

dform next_df : except_mode [src] :: next{'x} = slot{'x}  `"'"

