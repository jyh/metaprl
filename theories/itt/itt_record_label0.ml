(* labels as natural numberas *)

extends Itt_nat
extends Itt_struct2
extends Itt_struct3

open Base_meta
open Itt_int_ext
open Itt_struct
open Itt_struct3
open Dtactic
open Var
open Tactic_type
open Tactic_type.Tacticals
open Top_conversionals
open Itt_bool
open Itt_struct2


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
   sequent ['ext] { <H> >- "type"{label} }

interactive zeroMember {| intro [] |} :
   sequent ['ext] { <H> >- zero in label}

interactive nextMember {| intro [] |} :
   sequent [squash] { <H> >- 'x='y in label} -->
   sequent ['ext] { <H> >- next{'x} = next{'y} in label}

interactive labelInduction {| elim [ThinOption thinT] |} 'H :
   sequent ['ext] { <H>; n: label; <J['n]> >- 'C[zero] }  -->
   sequent ['ext] { <H>; n: label; <J['n]>; m: label;  z: 'C['m] >- 'C[next{'m}] }  -->
   sequent ['ext] { <H>; n: label; <J['n]> >- 'C['n] }

interactive labelBackInduction 'n bind{x.'C['x]} :
   sequent [squash]{ <H> >- 'n in label }  -->
   sequent ['ext] { <H> >- 'C['n] }  -->
   sequent ['ext] { <H>; m: label;  z: 'C[next{'m}] >- 'C['m] }  -->
   sequent ['ext] { <H>  >- 'C[zero] }

(**** equality ****)

interactive label_sqequal :
   sequent[squash] { <H> >-'n = 'm  in label} -->
   sequent['ext] { <H> >- 'n ~ 'm}

interactive decide_eq_label 'x 'y :
   [wf] sequent[squash] { <H> >- 'x in label} -->
   [wf] sequent[squash] { <H> >- 'y in label} -->
   [main] sequent['ext] { <H>; u:'x='y in label >- 'C} -->
   [main] sequent['ext] { <H>; u:not{.'x='y in label} >- 'C} -->
   sequent['ext] { <H> >- 'C}

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

