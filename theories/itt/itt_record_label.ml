include Itt_record_label0

open Base_meta
open Itt_int_ext
open Itt_struct
open Itt_struct2
open Base_dtactic
open Tactic_type.Conversionals
open Var
open Tactic_type
open Tactic_type.Tacticals
open Itt_bool
open Itt_record_label0

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Rformat
open Mp_resource

open Tactic_type

open Base_dtactic


(******************)
(*  Defenitions   *)
(******************)

(**** label ****)

declare label[t:s]

prim labelMember {| intro_resource []; eqcd_resource |} 'H :
   sequent ['ext] { 'H >- label[t:s] IN label } =
   it

let label_term = << label[x:s] >>
let label_opname = opname_of_term label_term
let is_label_term = TermOp.is_string_term label_opname
let dest_label = TermOp.dest_string_term label_opname
let mk_label_term = TermOp.mk_string_term label_opname



(**** equality ****)

define unfold_eq_label : eq_label[x:s,y:s]{'A;'B} <-->  meta_eq{label[x:s]; label[y:s]; 'A; 'B}

let reduce_eq_label =  unfold_eq_label andthenC reduce_meta_eq

(*! @docoff *)
let reduce_info =
   [<< eq_label[x:s,y:s]{'A;'B}  >>, reduce_eq_label]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info


(******************)
(*   Rules        *)
(******************)



prim reduce_eq_label_true {| intro_resource [] |} 'H:
   sequent[squash] {'H >- label[x:s] = label[y:s]  in label} -->
   sequent['ext] {'H >- eq_label[x:s,y:s]{'A;'B} ~ 'A}
      = it

interactive reduce_eq_label_false {| intro_resource [] |} 'H:
   sequent[squash] {'H >- not{.label[x:s] = label[y:s]  in label}} -->
   sequent['ext] {'H >- eq_label[x:s,y:s]{'A;'B} ~ 'B}


interactive_rw reduce_eq_label_true_rw :
   (label[x:s] = label[y:s]  in label) -->
   eq_label[x:s,y:s]{'A;'B} <--> 'A

interactive_rw reduce_eq_label_false_rw :
   (not{.label[x:s] = label[y:s]  in label}) -->
   eq_label[x:s,y:s]{'A;'B} <--> 'B


interactive not_eq_label  'H:
   sequent[squash] {'H >- eq_label[x:s,y:s]{."false";."true"} } -->
   sequent['ext] {'H >- not{.label[x:s] = label[y:s]  in label}}

let not_eq_labelT p =
      (not_eq_label (Sequent.hyp_count_addr p) thenT rw reduce_eq_label 0 thenT tryT (dT 0)) p

let into_resource =
   Mp_resource.improve intro_resource (<< not{.label[x:s] = label[y:s]  in label}>>, not_eq_labelT )

(******************)
(*   Tactic       *)
(******************)

let decideEqLabelT x y =
   let tac p =
      Itt_record_label0.decide_eq_label (Sequent.hyp_count_addr p) x y p
   in
      tac thenLT [tryT (dT 0);
                  tryT (dT 0);
                  tryT (rwhAll (firstC
                           [Itt_record_label0.reduce_eq_label_true_rw;
                            reduce_eq_label_true_rw])
                        thenAT nthHypT (-1)
                        thenT rwhAll reduce_ifthenelse_true);
                  tryT (rwhAll (firstC
                           [Itt_record_label0.reduce_eq_label_false_rw;
                            reduce_eq_label_false_rw])
                        thenAT nthHypT (-1)
                        thenT rwhAll reduce_ifthenelse_false)
                 ]


(******************)
(*  Display Forms *)
(******************)

dform label_df : except_mode[src] :: label[t:s] =  slot[t:s]

dform eq_label_df : except_mode[src] ::
   eq_label[x:s,y:s]{'A;'B} = ifthenelse{eq_label{label[x:s];label[y:s]};'A;'B}


