
include Itt_theory
include Itt_record_label
include Itt_record0
include Itt_struct3
include Itt_logic

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Var
open Tactic_type
open Tactic_type.Tacticals
open Base_dtactic
open Tactic_type.Conversionals

open Base_auto_tactic

open Itt_equal
open Itt_subtype
open Itt_struct
open Itt_record_label0
open Itt_record_label
open Itt_struct3
open Itt_logic

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_record%t"


(*! *)



(**********************************************)
(*                                            *)
(*  Records with token labels                 *)
(*                                            *)
(**********************************************)

(******************)
(*  Definitions   *)
(******************)


define unfoldRecordS : record[t:s]{'A} <--> record{label[t:s];'A}

define unfoldRecord : record[t:s]{'A;'R} <--> record{label[t:s];'A;'R}

define unfoldRcrd : rcrd[t:s]{'a;'r} <--> rcrd{label[t:s];'a;'r}

define unfoldRcrdS : rcrd[t:s]{'a} <--> rcrd[t:s]{'a;rcrd}

define unfoldField : field[t:s]{'r} <--> field{'r;label[t:s]}

define unfoldRecordOrt : record_ort[t:s]{'a;'R} <--> record_ort{label[t:s];'a;'R}

let unfoldAllT = rwaAll [unfoldRecordS;unfoldRecord;unfoldRcrdS;unfoldRcrd;unfoldField;unfoldRecordOrt]

(*! @docoff *)
let reduce_info =
   [<< rcrd[n:s]{'a} >>, unfoldRcrdS]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info

let intro_resource =
   Mp_resource.improve intro_resource (<<rcrd[n:s]{'a} = 'r in 'R>>, (rwh unfoldRcrdS 0 thenT dT 0))
let intro_resource =
   Mp_resource.improve intro_resource (<<'r = rcrd[n:s]{'a} in 'R>>, (rwh unfoldRcrdS 0 thenT dT 0))
(*! *)


(******************)
(*   Rules        *)
(******************)

(*** Typing ***)

interactive recordType {| intro_resource [] |} 'H :
   sequent[squash]{'H >- "type"{'A} } -->
   sequent['ext]  {'H >- "type"{record[n:s]{'A}} }

interactive recordType2 {| intro_resource [] |} 'H :
   sequent[squash]{'H >- "type"{'A} } -->
   sequent[squash]{'H >- "type"{'R} } -->
   sequent['ext]  {'H >- "type"{record[n:s]{'A;'R}} }

(*** Introductions ***)


interactive recordEqualS  'H:
   sequent[squash]{'H >- eq_label[n1:s,m:s]{
                            eq_label[n2:s,m:s]{
                               ('a1 ='a2 in 'A);                                  (* x1 = y = x2 *)
                               (rcrd[n1:s]{'a1;'r1} = 'r2 in record[m:s]{'A})};   (* x1 = y <> x2 *)
                               ('r1 = rcrd[n2:s]{'a2;'r2}  in record[m:s]{'A})}    (* x1 <> y  *)
                  } -->
   sequent['ext]  {'H >- rcrd[n1:s]{'a1;'r1} = rcrd[n2:s]{'a2;'r2} in record[m:s]{'A} }

let recordEqualST p =
      (recordEqualS (Sequent.hyp_count_addr p)
          thenT rw reduce_eq_label 0
          thenT tryT (rw reduce_eq_label 0)) p

let intro_resource =
   Mp_resource.improve intro_resource
      (<<rcrd[n1:s]{'a1;'r1} = rcrd[n2:s]{'a2;'r2} in record[m:s]{'A}>>, recordEqualST )


interactive recordIntroS  'H:
   sequent[squash]{'H >- eq_label[n:s,m:s]{('a IN 'A); ('r IN record[m:s]{'A})} } -->
   sequent['ext]  {'H >- rcrd[n:s]{'a;'r} IN record[m:s]{'A} }

let recordIntroST p =
      (recordIntroS (Sequent.hyp_count_addr p) thenT rw reduce_eq_label 0) p

let intro_resource =
   Mp_resource.improve intro_resource (<<rcrd[n:s]{'a;'r} IN record[m:s]{'A}>>, recordIntroST )

interactive recordIntro  {| intro_resource[] |} 'H:
   sequent[squash]{'H >- 'r = 's in record[n:s]{'A} } -->
   sequent[squash]{'H >- 'r = 's in 'R } -->
   sequent['ext]  {'H >- 'r = 's in record[n:s]{'A;'R} }

interactive recordIntro0  {| intro_resource[SelectOption 0] |} 'H:
   sequent[squash]{'H >- 'r IN 'R } -->
   [ort] sequent[squash]{'H; u:'R >- record_ort[n:s]{'a;'R} } -->
   sequent['ext]  {'H >- rcrd[n:s]{'a;'r} IN 'R }

(*** Reductions ***)

interactive_rw record_beta:
   field[n:s]{rcrd[m:s]{'a; 'r}} <--> eq_label[n:s,m:s]{'a;
                                                        field[n:s]{'r}}
let reduce_info =
   [<< field[n:s]{rcrd[m:s]{'a; 'r}} >>, (record_beta andthenC reduce_eq_label)]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info


interactive record_eta {| intro_resource [] |} 'H 'A:
   sequent[squash]{'H >- 'r IN record[n:s]{'A} } -->
   sequent['ext]  {'H >- rcrd[n:s]{field[n:s]{'r}; 'r} ~ 'r }

interactive_rw record_eta_rw  :
   ('r IN record[n:s]{top} ) -->
   rcrd[n:s]{field[n:s]{'r}; 'r} <--> 'r

interactive_rw record_exchange :
   rcrd[n:s]{'a; rcrd[m:s]{'b; 'r}} <--> eq_label[n:s,m:s]{rcrd[n:s]{'a;'r};
                                                           rcrd[m:s]{'b; rcrd[n:s]{'a; 'r}}}


(*** Eliminations ***)

interactive recordEliminationS {| elim_resource[] |} 'H 'J 'x:
   sequent['ext]  {'H; x:'A; r:record; 'J[rcrd[n:s]{'x;'r}] >- 'C[rcrd[n:s]{'x;'r}]} -->
   sequent['ext]  {'H; r:record[n:s]{'A}; 'J['r] >- 'C['r]}


interactive recordElimination  'H 'J 'x 'rr:
   [ort] sequent[squash]{'H; r:record[n:s]{'A;'R}; 'J['r]; x:'A; rr:'R >- record_ort[n:s]{'x;'R} } -->
   [main] sequent['ext]  {'H; x:'A; r:'R; 'J[rcrd[n:s]{'x;'r}] >- 'C[rcrd[n:s]{'x;'r}]} -->
   sequent['ext]  {'H; r:record[n:s]{'A;'R}; 'J['r] >- 'C['r]}

interactive recordElimination0  'H 'J  'x 'rr :
   sequent['ext]  {'H; r:record[n:s]{'A;'R}; 'J['r]; x:'A; rr:'R >- 'C['r]} -->
   sequent['ext]  {'H; r:record[n:s]{'A;'R}; 'J['r] >- 'C['r]}

interactive recordElimination1  'H 'J  'x 'rr :
   sequent['ext]  {'H; r:record[n:s]{'A;'R}; 'J['r]; x:'A; rr:'R >- 'C[rcrd[n:s]{'x;'rr}]} -->
   sequent['ext]  {'H; r:record[n:s]{'A;'R}; 'J['r] >- 'C['r]}

interactive recordElimination2  'H 'J  'x 'rr :
   sequent['ext]  {'H; r:record[n:s]{'A;'R}; 'J['r]; x:'A; rr:'R >- 'C['rr]} -->
   sequent['ext]  {'H; r:record[n:s]{'A;'R}; 'J['r] >- 'C['r]}


(*** Orthogonality ***)

interactive recordOrtIntro0 {| intro_resource[] |} 'H  :
   sequent['ext]  {'H  >- record_ort[n:s]{'a;record} }

interactive recordOrtIntroS 'H  'x  :
   [wf] sequent[squash]{'H >- "type"{record[m:s]{'A}} } -->
   [main] sequent[squash]{'H; x:'A >- eq_label[n:s,m:s]{.'a IN 'A;."true"} } -->
   sequent['ext]  {'H >- record_ort[n:s]{'a;record[m:s]{'A}} }

interactive recordOrtIntroSM 'H  'x  :
   [main] sequent[squash]  {'H; x:'A >- eq_label[n:s,m:s]{.'a IN 'A;."true"} } -->
   sequent['ext]  {'H; r:record[m:s]{'A}  >- record_ort[n:s]{'a;record[m:s]{'A}} }


interactive recordOrtIntro  'H  'x  :
   [wf] sequent[squash]{'H >- "type"{record[m:s]{'A;'R}} } -->
   [main] sequent[squash]  {'H; x:'A; r:'R >-  eq_label[n:s,m:s]{.'a IN 'A; record_ort[n:s]{'a;'R}} } -->
   sequent['ext]  {'H >- record_ort[n:s]{'a;record[m:s]{'A;'R}} }

interactive recordOrtIntroM 'H  'x  :
   [main] sequent[squash]  {'H; x:'A; r:'R >-  eq_label[n:s,m:s]{.'a IN 'A; record_ort[n:s]{'a;'R}} } -->
   sequent['ext]  {'H; r:record[m:s]{'A;'R}  >- record_ort[n:s]{'a;record[m:s]{'A;'R}} }


(******************)
(*  Tactics       *)
(******************)

(*** Ortogonality ***)

let recordOrtIntro0T p = recordOrtIntro0 ( Sequent.hyp_count_addr p) p

let recordOrtIntroST p =
   let m, _ = Sequent.hyp_indices p (-1) in
   let n= Sequent.hyp_count_addr p in
   let x= maybe_new_vars1 p "x" in
      ( (recordOrtIntroSM m x orelseT recordOrtIntroS n x)
        thenMT  rw reduce_eq_label 0
        thenT tryT (completeT (dT 0))
      ) p

let intro_resource =
   Mp_resource.improve intro_resource (<<record_ort[n:s]{'a;record[m:s]{'A}}>>,recordOrtIntroST)

let recordOrtIntroT p =
   let m, _ = Sequent.hyp_indices p (-1) in
   let n= Sequent.hyp_count_addr p in
   let x= maybe_new_vars1 p "x" in
      ((recordOrtIntroM m x orelseT recordOrtIntro n x) thenMT  rw reduce_eq_label 0) p


let repeatRecordOrtIntroT = (untilFailT recordOrtIntroT) thenT tryT (recordOrtIntroST orelseT recordOrtIntro0T)

let intro_resource =
   Mp_resource.improve intro_resource (<<record_ort[n:s]{'a;record[m:s]{'A;'R}}>>,repeatRecordOrtIntroT)


(*** Elimination ***)

let rec repeatRecordEliminationT n p =
   let j, k = Sequent.hyp_indices p n in
   let x,r = maybe_new_vars2 p "x" "r" in
      ((recordElimination j k x r
           thenMT tryT (repeatRecordEliminationT (n+1)))
          orelseT recordEliminationS j k x) p


let recordDefEliminationT n = repeatRecordEliminationT n thenAT tryT repeatRecordOrtIntroT

let recordEliminationT n p =
   let j, k = Sequent.hyp_indices p n in
   let x,r = maybe_new_vars2 p "x" "r" in
   try
      let sel = get_sel_arg p in
         if sel = 0 then recordElimination0 j k x r p else
         if sel = 1 then recordElimination1 j k x r p else
         if sel = 2 then recordElimination2 j k x r p else
            recordDefEliminationT n p
   with
         RefineError _ -> recordDefEliminationT n p

let elim_resource = Mp_resource.improve elim_resource (<<record[n:s]{'A;'R}>>, recordEliminationT)

(*** Reductions ***)

let record_exchangeC n =
      if n < 0 then
         raise (Invalid_argument "record_exchangeC: the argument should be not negative")
      else
         let rec aux i =
            if i = 0 then
               record_exchange andthenC reduce_eq_label
            else
               addrC [1] (aux (i -1))
         in
            aux n




(******************)
(*  Display Forms *)
(******************)

(*! @docoff *)



dform field_df : except_mode [src] :: field[t:s]{'r} = field{'r;label[t:s]}

dform recordS_df : except_mode [src] :: record[t:s]{'A} = record{label[t:s];'A}
dform record_df : except_mode [src] :: record[t:s]{'A;'R} = record{label[t:s];'A;'R}

dform rcrdS_df : except_mode [src] :: rcrd[t:s]{'a} = rcrd{label[t:s];'a}
dform rcrd_df : except_mode [src] :: rcrd[t:s]{'a;'r} = rcrd{label[t:s];'a;'r}

dform record_ort_df :  except_mode [src] :: record_ort[t:s]{'a;'r} = record_ort{label[t:s];'a;'r}






interactive test 'H :
   sequent['ext]  { 'H >-  'C}
