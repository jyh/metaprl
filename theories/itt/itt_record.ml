(*!
 * @begin[doc]
 * @module[Itt_record]
 *
 * This is a theory of record type.
 * Record type is defined as dependent intersection.
 * @end[doc]
 *)

(*! @doc{@parents} *)

extends Itt_record_label
extends Itt_record0
extends Itt_struct3
extends Itt_disect
extends Itt_logic
extends Itt_tsquash

(*! @docoff *)

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

(*! @doc{@terms} *)

(*! @docoff *)


define unfoldRcrd : rcrd[t:t]{'a;'r} <--> rcrd{label[t:t];'a;'r}

define unfoldRcrdS : rcrd[t:t]{'a} <--> rcrd[t:t]{'a;rcrd}

define unfoldField : field[t:t]{'r} <--> field{'r;label[t:t]}

define unfoldRecordS : record[t:t]{'A} <--> record{label[t:t];'A}

(*!
 * @begin[doc]
 * Records are defined as intersections. Dependent records are defined are defined as dependent intersectons:
 * @end[doc]
 *)

define unfoldRecordL : record[n:t]{self.'A['self];'R} <--> self: 'R  isect  record[n:t]{'A['self]}

define unfoldRecordR : record[n:t]{'A;a.'R['a]} <--> r: record[n:t]{'A}  isect   'R[field[n:t]{'r}]

define unfoldRecordI : record[n:t]{'A;'R} <--> record[n:t]{'A;x.'R}

(* let foldRecordI = makeFoldC  <<record{'n;'A;'R}>> unfoldRecordI *)

(*! @docoff *)


define unfoldFunctionOrt : function_ort{x.'f['x];'R} <--> (all x:'R. ('x = 'f['x] in 'R))

define unfoldRecordOrt : record_ort[t:t]{'a;'R} <-->  function_ort{r.rcrd[t:t]{'a;'r};'R}


(******************)
(*   Rules        *)
(******************)

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Typehood and equality}
 * @end[doc]
 *)

(*!
 * @begin[doc]
 * The following rule are derivable using the above definitions.
 * @end[doc]
 *)


(*** Typing ***)

interactive recordTypeS {| intro [] |} 'H :
   sequent[squash]{'H >- "type"{'A} } -->
   sequent['ext]  {'H >- "type"{record[n:t]{'A}} }

interactive field_member {| intro[] |} 'H:
   sequent[squash]{'H >- 'r in record[n:t]{'A} } -->
   sequent['ext]  {'H >- field[n:t]{'r} in 'A }

interactive recordTypeL {| intro [] |} 'H :
   sequent[squash]{'H >- "type"{'R} } -->
   sequent[squash]{'H; self:'R >- "type"{'A['self]} } -->
   sequent['ext]  {'H >- "type"{record[n:t]{self.'A['self];'R}} }

interactive recordTypeR {| intro [] |} 'H :
   sequent[squash]{'H >- "type"{'A} } -->
   sequent[squash]{'H; x:'A >- "type"{'R['x]} } -->
   sequent['ext]  {'H >- "type"{record[n:t]{'A;x.'R['x]}} }

interactive recordTypeI {| intro [] |} 'H :
   sequent[squash]{'H >- "type"{'A} } -->
   sequent[squash]{'H >- "type"{'R} } -->
   sequent['ext]  {'H >- "type"{record[n:t]{'A;'R}} }

(*** Reductions ***)

(*! @doc{@modsubsection{Reductions}} *)

interactive_rw record_beta1:
   field[n:t]{rcrd[n:t]{'a; 'r}} <--> 'a

interactive_rw record_beta2:
   (not{.label[m:t] = label[n:t] in label}) -->
   field[n:t]{rcrd[m:t]{'a; 'r}} <--> field[n:t]{'r}

interactive_rw record_beta:
   field[n:t]{rcrd[m:t]{'a; 'r}} <--> eq_label[m:t,n:t]{'a;
                                                        field[n:t]{'r}}

let record_beta_rw = record_beta thenC reduce_eq_label

let record_beta2_rw = record_beta2

let resource reduce +=
   [<< field[n:t]{rcrd[m:t]{'a; 'r}} >>, record_beta_rw;
    << field[n:t]{rcrd[n:t]{'a; 'r}} >>, record_beta1;
    << rcrd[n:t]{'a} >>, unfoldRcrdS]

let record_reduce = repeatC (higherC (firstC [unfoldRcrdS;record_beta1;record_beta_rw]))

let record_reduceT = rwhAll record_reduce


interactive record_eta {| intro [] |} 'H 'A:
   sequent[squash]{'H >- 'r in record[n:t]{'A} } -->
   sequent['ext]  {'H >- rcrd[n:t]{field[n:t]{'r}; 'r} ~ 'r }

interactive_rw record_eta_rw  :
   ('r in record[n:t]{top} ) -->
   rcrd[n:t]{field[n:t]{'r}; 'r} <--> 'r

interactive_rw record_exchange :
   rcrd[n:t]{'a; rcrd[m:t]{'b; 'r}} <--> eq_label[n:t,m:t]{rcrd[n:t]{'a;'r};
                                                           rcrd[m:t]{'b; rcrd[n:t]{'a; 'r}}}

(*** Introductions ***)
(*! @doc{@modsubsection{Introduction}} *)

interactive recordEqualS1 'H:
   [equality] sequent[squash]{'H >- not{.label[n:t]=label[m:t] in label} } -->
   [main] sequent[squash]{'H >- 'r1='r2 in record[m:t]{'A} } -->
   sequent['ext]  {'H >- rcrd[n:t]{'a;'r1}='r2 in record[m:t]{'A} }

interactive recordEqualS2 'H:
   [equality] sequent[squash]{'H >- not{.label[n:t]=label[m:t] in label} } -->
   [main] sequent[squash]{'H >- 'r1='r2 in record[m:t]{'A} } -->
   sequent['ext]  {'H >- 'r1=rcrd[n:t]{'a;'r2} in record[m:t]{'A} }

interactive recordEqualS3 'H:
   [equality] sequent[squash]{'H >- not{.label[n:t]=label[m:t] in label} } -->
   [main] sequent[squash]{'H >- 'r1='r2 in record[m:t]{'A} } -->
   sequent['ext]  {'H >- rcrd[n:t]{'a1;'r1}=rcrd[n:t]{'a2;'r2} in record[m:t]{'A} }

interactive recordEqualS4 'H:
   [equality] sequent[squash]{'H >- not{.label[n:t]=label[m:t] in label} } -->
   [main] sequent[squash]{'H >- 'r1=rcrd[m:t]{'a2;'r2} in record[m:t]{'A} } -->
   sequent['ext]  {'H >- rcrd[n:t]{'a1;'r1}=rcrd[m:t]{'a2;'r2} in record[m:t]{'A} }

interactive recordEqualS5 'H:
   [main] sequent[squash]{'H >- 'a1='a2 in 'A } -->
   sequent['ext]  {'H >- rcrd[m:t]{'a1;'r1}=rcrd[m:t]{'a2;'r2} in record[m:t]{'A} }
(*
interactive recordEqualS  'H:
   [main] sequent[squash]{'H >-
                          eq_label[n1:t,m:t]{
                            eq_label[n2:t,m:t]{
                               ('a1 ='a2 in 'A);                                  (* x1 = y = x2 *)
                               (rcrd[n1:t]{'a1;'r1} = 'r2 in record[m:t]{'A})};   (* x1 = y <> x2 *)
                               ('r1 = rcrd[n2:t]{'a2;'r2}  in record[m:t]{'A})}    (* x1 <> y  *)
                  } -->
   sequent['ext]  {'H >- rcrd[n1:t]{'a1;'r1} = rcrd[n2:t]{'a2;'r2} in record[m:t]{'A} }

interactive recordMemberS {| intro[] |} 'H:
   [main] sequent[squash]{'H >- eq_label[n:t,m:t]{('a in 'A); ('r in record[m:t]{'A})} } -->
   sequent['ext]  {'H >- rcrd[n:t]{'a;'r} in record[m:t]{'A} }
*)

let record_eqcdST p =
   let n = Sequent.hyp_count_addr p in
   let tac =
      rwh unfoldRcrdS 0 thenT
      firstT
      [recordEqualS5 n;
       recordEqualS4 n;
       recordEqualS3 n;
       recordEqualS2 n;
       recordEqualS1 n]
   in tac p

let resource intro += (<<'r1 = 'r2 in record[m:t]{'A} >>, wrap_intro record_eqcdST)

(*
let resource intro +=
   [(<<rcrd[n:t]{'a1} = 'r2 in record[m:t]{'A} >>, wrap_intro (rwh unfoldRcrdS 0));
    (<<'r2 = rcrd[n:t]{'a1} in record[m:t]{'A} >>, wrap_intro (rwh unfoldRcrdS 0))]
*)
(*
let rec record_eqcdS addr  =
   firstT
      [recordMemberS addr thenT eq_labelIntroT;
       recordEqualS addr thenT eq_labelIntroT thenT tryT eq_labelIntroT;
       recordEqualS2 addr thenLT [not_eq_labelT;record_eqcdS addr];
       recordEqualS1 addr thenLT [not_eq_labelT;record_eqcdS addr]]

*)

interactive recordTypeEliminationS {| elim [ThinOption thinT] |} 'H 'J 'v:
   [main] sequent ['ext] { 'H; u:"type"{record[n:t]{'A}}; v:"type"{'A}; 'J['u] >- 'C['u] } -->
   sequent ['ext] { 'H; u:"type"{record[n:t]{'A}}; 'J['u] >- 'C['u] }

interactive recordTypeEliminationL {| elim [ThinOption thinT] |} 'H 'J 'r 'v:
   [main] sequent ['ext] { 'H; u:"type"{record[n:t]{self.'A['self];'R}}; 'J['u] >- 'r in 'R } -->
   [main] sequent ['ext] { 'H; u:"type"{record[n:t]{self.'A['self];'R}}; v:"type"{'A['r]}; 'J['u] >- 'C['u] } -->
   sequent ['ext] { 'H; u:"type"{record[n:t]{self.'A['self];'R}}; 'J['u] >- 'C['u] }

interactive recordTypeEliminationR {| elim [ThinOption thinT] |} 'H 'J 'a 'v:
   [main] sequent ['ext] { 'H; u:"type"{record[n:t]{'A;x.'R['x]}}; 'J['u] >- 'a in 'A } -->
   [main] sequent ['ext] { 'H; u:"type"{record[n:t]{'A;x.'R['x]}}; v:"type"{'R['a]}; 'J['u] >- 'C['u] } -->
   sequent ['ext] { 'H; u:"type"{record[n:t]{'A;x.'R['x]}}; 'J['u] >- 'C['u] }

interactive recordEqualL {| intro[] |}  'H:
   [wf] sequent[squash]{'H >- "type"{record[n:t]{self.'A['self];'R}} } -->
   [main] sequent[squash]{'H >- 'r = 's in 'R } -->
   [main] sequent[squash]{'H >- 'r = 's in record[n:t]{'A['r]} } -->
   sequent['ext]  {'H >- 'r = 's in record[n:t]{self.'A['self];'R} }

interactive recordEqualR  {| intro[] |} 'H:
   [wf] sequent[squash]{'H >- "type"{record[n:t]{'A;x.'R['x]}} } -->
   [main] sequent[squash]{'H >- 'r = 's in record[n:t]{'A} } -->
   [main] sequent[squash]{'H >- 'r = 's in 'R[field[n:t]{'r}] } -->
   sequent['ext]  {'H >- 'r = 's in record[n:t]{'A;x.'R['x]} }

interactive recordEqualI {| intro[] |}  'H:
   [main] sequent[squash]{'H >- 'r = 's in record[n:t]{'A} } -->
   [main] sequent[squash]{'H >- 'r = 's in 'R } -->
   sequent['ext]  {'H >- 'r = 's in record[n:t]{'A;'R} }

interactive recordMemberOrt (* {| intro[AutoMustComplete] |} *) 'H 'u:
   [main] sequent[squash]{'H >- 'r in 'R } -->
   [ort] sequent[squash]{'H; u:'R >- record_ort[n:t]{'a;'R} } -->
   sequent['ext]  {'H >- rcrd[n:t]{'a;'r} in 'R }

interactive recordEqualOrt1 'H 'u:
   [main] sequent[squash]{'H >- 'r1 = 'r2 in 'R } -->
   [ort] sequent[squash]{'H; u:'R >- record_ort[n:t]{'a;'R} } -->
   sequent['ext]  {'H >- rcrd[n:t]{'a;'r1} = 'r2 in 'R }

interactive recordEqualOrt2 'H 'u:
   [main] sequent[squash]{'H >- 'r1 = 'r2 in 'R } -->
   [ort] sequent[squash]{'H; u:'R >- record_ort[n:t]{'a;'R} } -->
   sequent['ext]  {'H >- 'r1 = rcrd[n:t]{'a;'r2}  in 'R }

let recordOrtT p =
   let n= Sequent.hyp_count_addr p in
   let r= maybe_new_vars1 p "r" in
   let rrule =
      try
         let sel= get_sel_arg p in
            if sel=1 then recordEqualOrt1 else  if sel=2 then recordEqualOrt2 else recordMemberOrt
      with RefineError _ -> recordMemberOrt
   in
   let tac =
      rrule n r thenLT
         [idT;
          tryT (dT 0 thenWT tryT (typeAssertT thenT nthHypT (-2)));
         ]
   in tac p


(*
let record_eqcd p =
   let n= Sequent.hyp_count_addr p in
   let tac=
      firstT [record_eqcdS n; recordEqualI n; recordEqualL n; recordEqualR n]
      thenT rwh record_reduce 0
   in tac p

let record_repeat_eqcd =
   rwh unfoldRcrdS 0 thenT record_eqcd thenT untilFailT record_eqcd

let resource intro += [
   (<<'r='s in record[m:t]{'A}>>, wrap_intro record_repeat_eqcd);
   (<<'r='s in record[m:t]{'A;'R}>>, wrap_intro record_repeat_eqcd);
   (<<'r='s in record[m:t]{'A;a.'R['a]}>>, wrap_intro record_repeat_eqcd);
   (<<'r='s in record[m:t]{self.'A['self];'R}>>, wrap_intro record_repeat_eqcd)
]
*)

(*** Eliminations ***)
(*! @doc{@modsubsection{Elimination}} *)

(* Single Records *)

interactive recordEliminationS {| elim[] |} 'H 'J 'x:
   [main] sequent['ext]  {'H; x:'A; r:record; 'J[rcrd[n:t]{'x;'r}] >- 'C[rcrd[n:t]{'x;'r}]} -->
   sequent['ext]  {'H; r:record[n:t]{'A}; 'J['r] >- 'C['r]}

(* Left-associated Records *)

interactive recordEliminationL2 {| elim[] |} 'H 'J   bind{rr,x.'C['rr;'x]} :
   [main] sequent['ext]  {'H; r:record[n:t]{self.'A['self];'R}; 'J['r]; rr:'R; x:'A['rr] >- 'C['rr;'x]} -->
   sequent['ext]  {'H; r:record[n:t]{self.'A['self];'R}; 'J['r] >- 'C['r; field[n:t]{'r}]}

interactive recordEliminationL1  'H 'J  'x :
   [main] sequent['ext]  {'H; r:'R; x:'A['r]; 'J  >- 'C[rcrd[n:t]{'x;'r}]} -->
   sequent['ext]  {'H; r:record[n:t]{self.'A['self];'R}; 'J >- 'C['r]}

interactive recordEliminationL 'H 'J 'x 'rr:
   [ort] sequent[squash]{'H; r:record[n:t]{self.'A['self];'R}; 'J['r]; rr:'R; x:'A['rr]
                                                                >- record_ort[n:t]{'x;'R} } -->
   [main] sequent['ext]  {'H; r:'R; x:'A['r]; 'J[rcrd[n:t]{'x;'r}] >- 'C[rcrd[n:t]{'x;'r}]} -->
   sequent['ext]  {'H; r:record[n:t]{self.'A['self];'R}; 'J['r] >- 'C['r]}

(* Right-assotiated Records *)

interactive recordEliminationR2 {| elim[] |} 'H 'J    bind{rr,z.'C['rr;'z]}:
   [main] sequent['ext]  {'H; r:record[n:t]{'A;x.'R['x]}; 'J['r]; x:'A; rr:'R['x] >- 'C['rr;'x]} -->
   sequent['ext]  {'H; r:record[n:t]{'A;x.'R['x]}; 'J['r] >- 'C['r; field[n:t]{'r}]}

interactive recordEliminationR1 'H 'J   :
   [main] sequent['ext]  {'H; x:'A; r:'R['x]; 'J  >- 'C[rcrd[n:t]{'x;'r}]} -->
   sequent['ext]  {'H; r:record[n:t]{'A;x.'R['x]}; 'J >- 'C['r]}

interactive recordEliminationR 'H 'J 'rr:
   [ort] sequent[squash]{'H; r:record[n:t]{'A;x.'R['x]}; 'J['r]; x:'A; rr:'R['x] >- record_ort[n:t]{'x;'R['x]} } -->
   [main] sequent['ext]  {'H; x:'A; r:'R['x]; 'J[rcrd[n:t]{'x;'r}] >- 'C[rcrd[n:t]{'x;'r}]} -->
   sequent['ext]  {'H; r:record[n:t]{'A;x.'R['x]}; 'J['r] >- 'C['r]}

(* Independent Records *)

interactive recordEliminationI2  'H 'J  'x 'rr :
   [main] sequent['ext]  {'H; r:record[n:t]{'A;'R}; 'J['r]; x:'A; rr:'R >- 'C['rr]} -->
   sequent['ext]  {'H; r:record[n:t]{'A;'R}; 'J['r] >- 'C['r]}

interactive recordEliminationI1  'H 'J  'x :
   [main] sequent['ext]  {'H; x:'A; r:'R; 'J  >- 'C[rcrd[n:t]{'x;'r}]} -->
   sequent['ext]  {'H; r:record[n:t]{'A;'R}; 'J >- 'C['r]}

interactive recordEliminationI  'H 'J 'x 'rr:
   [ort] sequent[squash]{'H; r:record[n:t]{'A;'R}; 'J['r]; x:'A; rr:'R >- record_ort[n:t]{'x;'R} } -->
   [main] sequent['ext]  {'H; x:'A; r:'R; 'J[rcrd[n:t]{'x;'r}] >- 'C[rcrd[n:t]{'x;'r}]} -->
   sequent['ext]  {'H; r:record[n:t]{'A;'R}; 'J['r] >- 'C['r]}


(*! @docoff *)


let recordL_elim n p =
 let j, k = Sequent.hyp_indices p n in
 let x,r = maybe_new_vars2 p "x" "r" in
 let tac =
    (recordEliminationL1 j k x orelseT recordEliminationL j k x r)
    thenT
       ifLabT "ort"
                (tryT (dT 0 thenWT tryT (typeAssertT thenT nthHypT (-2))))
       (*else*) (record_reduceT thenMT tryT (dT n))
 in
    tac p

let recordR_elim n p =
 let j, k = Sequent.hyp_indices p n in
 let r = maybe_new_vars1 p "r" in
 let tac =
    (recordEliminationR1 j k orelseT recordEliminationR j k r)
    thenT
       ifLabT "ort"
                (tryT (dT 0 thenWT tryT (typeAssertT thenT nthHypT (-1))))
       (*else*) (record_reduceT thenMT tryT (dT (n+1)))
 in
    tac p

let recordI_elim n p =
 let j, k = Sequent.hyp_indices p n in
 let x,r = maybe_new_vars2 p "x" "r" in
 let tac =
    (recordEliminationI1 j k x orelseT recordEliminationI j k x r)
    thenT
       ifLabT "ort"
                (tryT (dT 0 thenWT tryT (typeAssertT thenT nthHypT (-1))))
       (*else*) (record_reduceT thenMT tryT (dT (n+1)))
 in
    tac p

let resource elim += [
   (<<record[m:t]{'A;'R}>>,recordI_elim);
   (<<record[m:t]{'A;a.'R['a]}>>,recordR_elim);
   (<<record[m:t]{self.'A['self];'R}>>,recordL_elim)
]




(*** Orthogonality ***)
(*! @doc{@modsubsection{Orthogonality}} *)

interactive functionOrtDinter {| intro[] |} 'H 'b :
   [wf] sequent[squash]{'H >- "type"{bisect{'A;a.'B['a]}} } -->
   [main] sequent[squash]{'H; a:'A; b:'B['a] >- function_ort{x.'f['x];'A} } -->
   [main] sequent[squash]{'H; a:'A; b:'B['a] >- function_ort{x.'f['x];'B['a]} } -->
   sequent['ext]  {'H >-  function_ort{x.'f['x]; bisect{'A;a.'B['a]}} }



interactive recordOrtIntro0 {| intro[] |} 'H  :
   sequent['ext]  {'H  >- record_ort[n:t]{'a;record} }

interactive recordOrtIntroTop {| intro[] |} 'H  :
   [wf] sequent[squash]  {'H  >- "type"{tsquash{'A}} } -->
   sequent['ext]  {'H  >- record_ort[n:t]{'a;tsquash{'A}} }

interactive recordOrtIntroS1 'H :
   [wf] sequent[squash]{'H >- "type"{record[m:t]{'A}} } -->
   [main] sequent[squash]{'H >- not{. label[n:t]=label[m:t] in label} } -->
   sequent['ext]  {'H >- record_ort[n:t]{'a;record[m:t]{'A}} }

interactive recordOrtIntroS2 'H  'x  :
   [wf] sequent[squash]{'H >- "type"{record[n:t]{'A}} } -->
   [main] sequent[squash]{'H; x:'A >- 'x='a in 'A } -->
   sequent['ext]  {'H >- record_ort[n:t]{'a;record[n:t]{'A}} }

let recordOrtIntroST p =
   let n= Sequent.hyp_count_addr p in
   let x= maybe_new_vars1 p "x" in
   let tac =
      recordOrtIntroS2 n x orelseT recordOrtIntroS1 n
   in tac p

let resource intro += (<<record_ort[n:t]{'a;record[m:t]{'A}}>>,wrap_intro recordOrtIntroST)

interactive recordOrtIntroL  'H  'x 'r:
   [wf] sequent[squash]{'H >- "type"{record[m:t]{self.'A['self];'R}} } -->
   [main] sequent[squash]  {'H; r:'R; x:'A['r] >- record_ort[n:t]{'a;'R}}  -->
   [main] sequent[squash]  {'H; r:'R; x:'A['r] >- record_ort[n:t]{'a;record[m:t]{'A['r]}}}  -->
   sequent['ext]  {'H >- record_ort[n:t]{'a;record[m:t]{self.'A['self];'R}} }

let recordOrtIntroLT p =
   let n= Sequent.hyp_count_addr p in
   let x,r= maybe_new_vars2 p "x" "r" in
   let tac =
      recordOrtIntroL n x r thenLT
         [idT;
          tryT (dT 0 thenWT tryT (typeAssertT thenT nthHypT (-2)));
          rwh record_reduce 0 thenT tryT recordOrtIntroST thenWT tryT (dT 0 thenT typeAssertT thenT nthHypT (-1));
         ]
   in tac p

let resource intro += (<<record_ort[n:t]{'a;record[m:t]{self.'A['self];'R}}>>,wrap_intro recordOrtIntroLT)

interactive recordOrtIntroR  'H  'r :
   [wf] sequent[squash]{'H >- "type"{record[m:t]{'A;x.'R['x]}} } -->
   [main] sequent[squash]  {'H; x:'A; r:'R['x] >- record_ort[n:t]{'a;'R['x]} } -->
   [main] sequent[squash]  {'H; x:'A; r:'R['x] >- record_ort[n:t]{'a;record[m:t]{'A}}}  -->
   sequent['ext]  {'H >- record_ort[n:t]{'a;record[m:t]{'A;x.'R['x]}} }

let recordOrtIntroRT p =
   let n= Sequent.hyp_count_addr p in
   let r= maybe_new_vars1 p "r" in
   let tac =
      recordOrtIntroR n r thenLT
         [idT;
          tryT (dT 0 thenWT tryT (typeAssertT thenT nthHypT (-1)));
          tryT recordOrtIntroST thenWT tryT (dT 0 thenT typeAssertT thenT nthHypT (-2));
         ]
   in tac p

let resource intro += (<<record_ort[n:t]{'a;record[m:t]{'A;x.'R['x]}}>>,wrap_intro recordOrtIntroRT)

interactive recordOrtIntroI  'H  'x 'r :
   [wf] sequent[squash]{'H >- "type"{record[m:t]{'A;'R}} } -->
   [main] sequent[squash]  {'H; x:'A; r:'R >- record_ort[n:t]{'a;'R} } -->
   [main] sequent[squash]  {'H; x:'A; r:'R >- record_ort[n:t]{'a;record[m:t]{'A}}} -->
   sequent['ext]  {'H >- record_ort[n:t]{'a;record[m:t]{'A;'R}} }

let recordOrtIntroIT p =
   let n= Sequent.hyp_count_addr p in
   let x,r= maybe_new_vars2 p "x" "r" in
   let tac =
      recordOrtIntroI n x r thenLT
         [idT;
          tryT (dT 0 thenWT tryT (typeAssertT thenT nthHypT (-1)));
          tryT recordOrtIntroST thenWT tryT (dT 0 thenT typeAssertT thenT nthHypT (-2));
         ]
   in tac p

let resource intro += (<<record_ort[n:t]{'a;record[m:t]{'A;'R}}>>,wrap_intro recordOrtIntroIT)


(******************)
(*  Tactics       *)
(******************)

(*! @docoff *)




(*
let elim0 rule p n =
   let j, k = Sequent.hyp_indices p n in
   let bind =
      try
         let b = get_with_arg p in
            if is_bind2_term b then
               b
            else
               raise (RefineError ("recordElimination2",
                                   StringTermError ("need a \"bind{r,x.'A['r;'x]}\" term: ", b)))
      with
         RefineError _ ->
            let r, record = Sequent.nth_hyp p n in
            let x = field_name record
            let rr,xx = maybe_new_vars2 rr xx in
            let field = mk_rcrd_term x
            let concl = (Sequent.concl p) in
            let concl1 = var_subst concl r.x

            mk_bind2_term z (var_subst ) a z)
*)

(*** Ortogonality ***)
(*
let recordOrtIntro0T p = recordOrtIntro0 ( Sequent.hyp_count_addr p) p

let recordOrtIntroST p =
   let m, _ = Sequent.hyp_indices p (-1) in
   let n= Sequent.hyp_count_addr p in
   let x= maybe_new_vars1 p "x" in
      ( (recordOrtIntroSM m x orelseT recordOrtIntroS n x)
        thenMT  rw reduce_eq_label 0
        thenWT tryT (typeAssertT thenT trivialT)
        thenT tryT (completeT (dT 0))
      ) p

let resource intro += (<<record_ort[n:t]{'a;record[m:t]{'A}}>>, wrap_intro recordOrtIntroST)

let recordOrtIntroT p =
   let m, _ = Sequent.hyp_indices p (-1) in
   let n= Sequent.hyp_count_addr p in
   let x= maybe_new_vars1 p "x" in
      ((recordOrtIntroM m x orelseT recordOrtIntro n x) thenMT  rw reduce_eq_label 0) p


let repeatRecordOrtIntroT = (untilFailT recordOrtIntroT) thenT tryT (recordOrtIntroST orelseT recordOrtIntro0T)

let resource intro += (<<record_ort[n:t]{'a;record[m:t]{'A;'R}}>>, wrap_intro repeatRecordOrtIntroT)

*)
(*** Elimination ***)
(*
let makeElimTac1 rule p  =
 let j, k = Sequent.hyp_indices p n in
   let x = maybe_new_vars2 p "x" "r" in
      tac j k x p


let makeElimTac2 rule p  =
 let j, k = Sequent.hyp_indices p n in
   let x,r = maybe_new_vars2 p "x" "r" in
      tac j k x r p

let repeatRecEl tac n p =
   dT n thenMT dT (n+1)
      tac n thenMT tryT (tac (n+1))
          orelseT recordEliminationS j k x) p
*)
(*
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
         if sel = 0 then recordElimination2 j k x r p else
            (recordElimination1 j k x r orelse recordElimination j k x r) p
   with
         RefineError _ -> recordDefEliminationT n p

let resource elim += (<<record[n:t]{'A;'R}>>, recordEliminationT)
*)
(*** Reductions ***)

let record_exchangeC n =
      if n < 0 then
         raise (Invalid_argument "record_exchangeC: the argument should be not negative")
      else
         let rec aux i =
            if i = 0 then
               record_exchange thenC reduce_eq_label
            else
               addrC [1] (aux (i -1))
         in
            aux n




(******************)
(*  Display Forms *)
(******************)

(*! @docoff *)

declare subrecord{'A}
declare self{'self}

declare self[n:t]{'x}

dform self_df : except_mode [src] ::  self{'self} = `""

(*
dform field_self  : except_mode [src] ::  field[t:t]{self{'self}} = label[t:t]
*)

dform field_df : except_mode [src] :: field[t:t]{'r} = field{'r;label[t:t]}

dform self_lab_df : except_mode [src] ::  self[n:t]{'x} = field[n:t]{self{'x}}



dform subrecord_df : except_mode [src] :: subrecord{'r} = 'r

dform subrcrdS_df : except_mode [src] :: subrecord{rcrd[n:t]{'a}}
   = label[n:t] `"=" slot{'a}

dform subrecordS_df : except_mode [src] :: subrecord{record[n:t]{'a}}
   = label[n:t] `":" slot{'a}

dform subrcrd_df : except_mode [src] :: subrecord{rcrd[n:t]{'a;'r}}
   =  subrecord{'r} `";" \space subrecord{rcrd[n:t]{'a}}

dform subrecordI_df : except_mode [src] :: subrecord{record[n:t]{'a;'r}}
   = subrecord{record[n:t]{'a}} `";" \space subrecord{'r}

dform subrecordL_df : except_mode [src] :: subrecord{record[n:t]{self.'a['self];'r}}
   = subrecord{'r} `";" \space subrecord{record[n:t]{'a[self{'self}]}}

dform subrecordR_df : except_mode [src] :: subrecord{record[n:t]{'a;x.'r['x]}}
   = subrecord{record[n:t]{'a}} `";" \space subrecord{'r[self[n:t]{'x}]}





dform rcrdS_df : except_mode [src] :: rcrd[n:t]{'a}
   = `"{" subrecord{rcrd[n:t]{'a}} `"}"

dform rcrd_df : except_mode [src] :: rcrd[n:t]{'a;'r}
   = `"{" subrecord{rcrd[n:t]{'a;'r}} `"}"

dform recordS_df : except_mode [src] :: record[n:t]{'a}
   = `"{" subrecord{record[n:t]{'a}} `"}"

dform recordI_df : except_mode [src] :: record[n:t]{'a;'r}
   = `"{" subrecord{record[n:t]{'a;'r}} `"}"

dform recordR_df : except_mode [src] :: record[n:t]{self.'a['self];'r}
   = `"{" subrecord{record[n:t]{self.'a['self];'r}} `"}"

dform recordL_df : except_mode [src] :: record[n:t]{'a;x.'r['x]}
   = `"{" subrecord{record[n:t]{'a;x.'r['x]}} `"}"




dform functionOrt_df : except_mode [src] :: function_ort{x.'f['x];'R}
     =  slot{'f[bf{cdot}]} perp slot{'R}

dform recordOrt_df : except_mode [src] :: record_ort[n:t]{'a;'R}
     =   rcrd[n:t]{'a} perp 'R

