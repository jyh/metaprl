doc <:doc<
   @begin[doc]
   @module[Itt_record]

   This is a theory of record type.
   Record type is defined as dependent intersection.
   @end[doc]
>>

doc <:doc< @doc{@parents} >>

extends Itt_record_label
extends Itt_record0
extends Itt_struct3
extends Itt_disect
extends Itt_logic
extends Itt_tsquash
extends Itt_bisect

doc <:doc< @docoff >>

open Lm_debug
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError

open Tactic_type
open Tactic_type.Tacticals
open Auto_tactic
open Dtactic
open Top_conversionals

open Itt_equal
open Itt_struct
open Itt_record_label

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_record%t"

doc <:doc< >>

(**********************************************)
(*                                            *)
(*  Records with token labels                 *)
(*                                            *)
(**********************************************)

(******************)
(*  Definitions   *)
(******************)

doc <:doc< @doc{@terms} >>

doc <:doc< @docoff >>

define unfoldRcrd : rcrd[t:t]{'a;'r} <--> rcrd{label[t:t];'a;'r}

define unfoldRcrdS {| reduce |} : rcrd[t:t]{'a} <--> rcrd[t:t]{'a;rcrd}

define unfoldField : field[t:t]{'r} <--> field{'r;label[t:t]}

define unfoldRecordS : record[t:t]{'A} <--> record{label[t:t];'A}

doc <:doc<
   @begin[doc]
   Records are defined as intersections. Dependent records are defined as dependent intersections:
   @end[doc]
>>

define unfoldRecordL : record[n:t]{self.'A['self];'R} <--> self: 'R  isect  record[n:t]{'A['self]}

define unfoldRecordR : record[n:t]{'A;a.'R['a]} <--> r: record[n:t]{'A}  isect   'R[field[n:t]{'r}]

define unfoldRecordI : record[n:t]{'A;'R} <--> record[n:t]{'A;x.'R}

(* let foldRecordI = makeFoldC  <<record{'n;'A;'R}>> unfoldRecordI *)

doc <:doc< @docoff >>

define unfoldFunctionOrt : function_ort{x.'f['x];'R} <--> (all x:'R. ('x = 'f['x] in 'R))

define unfoldRecordOrt : record_ort[t:t]{'a;'R} <-->  function_ort{r.rcrd[t:t]{'a;'r};'R}

(****************************)
(* Constructors/destructors *)
(****************************)

let field_term = <<'a^fld>>
let field_opname = opname_of_term field_term
let dest_field t =
   match dest_token_simple_term field_opname t with
      f, [t] ->
         t, f
    | _ -> raise(RefineError("dest_field", StringError "not a field term"))
let mk_field_term t f =
   mk_token_simple_term field_opname f [t]

(******************)
(*   Rules        *)
(******************)

doc <:doc<
   @begin[doc]
   @rules
   @modsubsection{Typehood and equality}
   @end[doc]
>>

doc <:doc<
   @begin[doc]
   The following rule are derivable using the above definitions.
   @end[doc]
>>

(*** Typing ***)

interactive recordTypeS {| intro [] |} :
   sequent{ <H> >- "type"{'A} } -->
   sequent{ <H> >- "type"{record[n:t]{'A}} }

interactive field_member {| intro[AutoMustComplete] |} :
   sequent{ <H> >- 'r in record[n:t]{'A} } -->
   sequent{ <H> >- field[n:t]{'r} in 'A }

interactive recordTypeL {| intro [] |} :
   sequent{ <H> >- "type"{'R} } -->
   sequent{ <H>; self:'R >- "type"{'A['self]} } -->
   sequent{ <H> >- "type"{record[n:t]{self.'A['self];'R}} }

interactive recordTypeR {| intro [] |} :
   sequent{ <H> >- "type"{'A} } -->
   sequent{ <H>; x:'A >- "type"{'R['x]} } -->
   sequent{ <H> >- "type"{record[n:t]{'A;x.'R['x]}} }

interactive recordTypeI {| intro [] |} :
   sequent{ <H> >- "type"{'A} } -->
   sequent{ <H> >- "type"{'R} } -->
   sequent{ <H> >- "type"{record[n:t]{'A;'R}} }

(*** Reductions ***)

doc <:doc< @doc{@modsubsection{Reductions}} >>

interactive_rw record_beta1 {| reduce |} :
   field[n:t]{rcrd[n:t]{'a; 'r}} <--> 'a

interactive_rw record_beta2:
   (label[m:t] <> label[n:t] in label) -->
   field[n:t]{rcrd[m:t]{'a; 'r}} <--> field[n:t]{'r}

interactive_rw record_beta:
   field[n:t]{rcrd[m:t]{'a; 'r}} <--> eq_label[m:t,n:t]{'a;
                                                        field[n:t]{'r}}

let record_beta_rw = record_beta thenC reduce_eq_label

let record_beta2_rw = record_beta2

let resource reduce +=
   << field[n:t]{rcrd[m:t]{'a; 'r}} >>, record_beta_rw

let record_reduce = repeatC (higherC (firstC [unfoldRcrdS;record_beta1;record_beta_rw]))

let record_reduceT = rwhAll record_reduce

interactive record_eta {| intro [] |} 'A:
   sequent{ <H> >- 'r in record[n:t]{'A} } -->
   sequent{ <H> >- rcrd[n:t]{field[n:t]{'r}; 'r} ~ 'r }

interactive_rw record_eta_rw  :
   ('r in recordTop ) -->
   rcrd[n:t]{field[n:t]{'r}; 'r} <--> 'r

interactive_rw record_exchange :
   rcrd[n:t]{'a; rcrd[m:t]{'b; 'r}} <--> eq_label[n:t,m:t]{rcrd[n:t]{'a;'r};
                                                           rcrd[m:t]{'b; rcrd[n:t]{'a; 'r}}}

interactive_rw record_same_reduce {| reduce |}:  (* This should not be in eval, but in autoC *)
   rcrd[n:t]{'a; rcrd[n:t]{'b; 'r}} <--> rcrd[n:t]{'a;'r}


(*** Introductions ***)
doc <:doc< @doc{@modsubsection{Introduction}} >>

interactive recordIntroE1 {| intro[] |} :
   sequent{ <H> >- 'r in recordTop } -->
   sequent{ <H> >- rcrd[n:t]{'a;'r} in recordTop }

interactive recordIntroE2 {| intro[] |} :
   sequent{ <H> >- rcrd[n:t]{'a} in recordTop }

interactive recordEqualS1 :
   [equality] sequent{ <H> >- label[n:t]<>label[m:t] in label } -->
   [main] sequent{ <H> >- 'r1='r2 in record[m:t]{'A} } -->
   sequent{ <H> >- rcrd[n:t]{'a;'r1}='r2 in record[m:t]{'A} }

interactive recordEqualS2 :
   [equality] sequent{ <H> >- label[n:t]<>label[m:t] in label } -->
   [main] sequent{ <H> >- 'r1='r2 in record[m:t]{'A} } -->
   sequent{ <H> >- 'r1=rcrd[n:t]{'a;'r2} in record[m:t]{'A} }

interactive recordEqualS3 :
   [equality] sequent{ <H> >- label[n:t]<>label[m:t] in label } -->
   [main] sequent{ <H> >- 'r1='r2 in record[m:t]{'A} } -->
   sequent{ <H> >- rcrd[n:t]{'a1;'r1}=rcrd[n:t]{'a2;'r2} in record[m:t]{'A} }

interactive recordEqualS4 :
   [equality] sequent{ <H> >- label[n:t]<>label[m:t] in label } -->
   [main] sequent{ <H> >- 'r1=rcrd[m:t]{'a2;'r2} in record[m:t]{'A} } -->
   sequent{ <H> >- rcrd[n:t]{'a1;'r1}=rcrd[m:t]{'a2;'r2} in record[m:t]{'A} }

interactive recordEqualS5 :
   [main] sequent{ <H> >- 'a1='a2 in 'A } -->
   sequent{ <H> >- rcrd[m:t]{'a1;'r1}=rcrd[m:t]{'a2;'r2} in record[m:t]{'A} }
(*
interactive recordEqualS :
   [main] sequent{ <H> >-
                          eq_label[n1:t,m:t]{
                            eq_label[n2:t,m:t]{
                               ('a1 ='a2 in 'A);                                  (* x1 = y = x2 *)
                               (rcrd[n1:t]{'a1;'r1} = 'r2 in record[m:t]{'A})};   (* x1 = y <> x2 *)
                               ('r1 = rcrd[n2:t]{'a2;'r2}  in record[m:t]{'A})}    (* x1 <> y  *)
                  } -->
   sequent{ <H> >- rcrd[n1:t]{'a1;'r1} = rcrd[n2:t]{'a2;'r2} in record[m:t]{'A} }

interactive recordMemberS {| intro[] |} :
   [main] sequent{ <H> >- eq_label[n:t,m:t]{('a in 'A); ('r in record[m:t]{'A})} } -->
   sequent{ <H> >- rcrd[n:t]{'a;'r} in record[m:t]{'A} }
*)

let record_eqcdST =
   rwh unfoldRcrdS 0 thenT firstT [recordEqualS5; recordEqualS4; recordEqualS3; recordEqualS2; recordEqualS1]

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

interactive recordTypeEliminationS {| elim [ThinOption thinT] |} 'H :
   [main] sequent { <H>; u:"type"{record[n:t]{'A}}; v:"type"{'A}; <J['u]> >- 'C['u] } -->
   sequent { <H>; u:"type"{record[n:t]{'A}}; <J['u]> >- 'C['u] }

interactive recordTypeEliminationL {| elim [ThinOption thinT] |} 'H 'r :
   [main] sequent { <H>; u:"type"{record[n:t]{self.'A['self];'R}}; <J['u]> >- 'r in 'R } -->
   [main] sequent { <H>; u:"type"{record[n:t]{self.'A['self];'R}}; v:"type"{'A['r]}; <J['u]> >- 'C['u] } -->
   sequent { <H>; u:"type"{record[n:t]{self.'A['self];'R}}; <J['u]> >- 'C['u] }

interactive recordTypeEliminationR {| elim [ThinOption thinT] |} 'H 'a :
   [main] sequent { <H>; u:"type"{record[n:t]{'A;x.'R['x]}}; <J['u]> >- 'a in 'A } -->
   [main] sequent { <H>; u:"type"{record[n:t]{'A;x.'R['x]}}; v:"type"{'R['a]}; <J['u]> >- 'C['u] } -->
   sequent { <H>; u:"type"{record[n:t]{'A;x.'R['x]}}; <J['u]> >- 'C['u] }

interactive recordEqualL {| intro[] |} :
   [wf] sequent{ <H> >- "type"{record[n:t]{self.'A['self];'R}} } -->
   [main] sequent{ <H> >- 'r = 's in 'R } -->
   [main] sequent{ <H> >- 'r = 's in record[n:t]{'A['r]} } -->
   sequent{ <H> >- 'r = 's in record[n:t]{self.'A['self];'R} }

interactive recordEqualR  {| intro[] |} :
   [wf] sequent{ <H> >- "type"{record[n:t]{'A;x.'R['x]}} } -->
   [main] sequent{ <H> >- 'r = 's in record[n:t]{'A} } -->
   [main] sequent{ <H> >- 'r = 's in 'R[field[n:t]{'r}] } -->
   sequent{ <H> >- 'r = 's in record[n:t]{'A;x.'R['x]} }

interactive recordEqualI {| intro[] |} :
   [main] sequent{ <H> >- 'r = 's in record[n:t]{'A} } -->
   [main] sequent{ <H> >- 'r = 's in 'R } -->
   sequent{ <H> >- 'r = 's in record[n:t]{'A;'R} }

interactive recordMemberOrt (* {| intro[AutoMustComplete] |} *) :
   [main] sequent{ <H> >- 'r in 'R } -->
   [ort] sequent{ <H>; u:'R >- record_ort[n:t]{'a;'R} } -->
   sequent{ <H> >- rcrd[n:t]{'a;'r} in 'R }

interactive recordEqualOrt1 :
   [main] sequent{ <H> >- 'r1 = 'r2 in 'R } -->
   [ort] sequent{ <H>; r:'R >- record_ort[n:t]{'a;'R} } -->
   sequent{ <H> >- rcrd[n:t]{'a;'r1} = 'r2 in 'R }

interactive recordEqualOrt2 :
   [main] sequent{ <H> >- 'r1 = 'r2 in 'R } -->
   [ort] sequent{ <H>; r:'R >- record_ort[n:t]{'a;'R} } -->
   sequent{ <H> >- 'r1 = rcrd[n:t]{'a;'r2}  in 'R }

let recordOrtT = funT (fun p ->
   let rrule =
      try
         let sel= get_sel_arg p in
            if sel=1 then recordEqualOrt1 else  if sel=2 then recordEqualOrt2 else recordMemberOrt
      with RefineError _ -> recordMemberOrt
   in
      rrule thenLT
         [idT;
          tryT (dT 0 thenWT tryT (typeAssertT thenT nthHypT (-2)));
         ])

(*
let record_eqcd =
   firstT [record_eqcdS; recordEqualI; recordEqualL; recordEqualR] thenT rwh record_reduce 0

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
doc <:doc< @doc{@modsubsection{Elimination}} >>

(* Single Records *)

interactive recordEliminationS {| elim[] |} 'H :
   [main] sequent{ <H>; x:'A; dum:record; <J[rcrd[n:t]{'x;'dum}]> >- 'C[rcrd[n:t]{'x;'dum}]} -->
   sequent{ <H>; r:record[n:t]{'A}; <J['r]> >- 'C['r]}

(* Left-associated Records *)

interactive recordEliminationL2 {| elim[] |} 'H bind{rr,x.'C['rr;'x]} :
   [main] sequent{ <H>; r:record[n:t]{self.'A['self];'R}; <J['r]>; rr:'R; x:'A['rr] >- 'C['rr;'x]} -->
   sequent{ <H>; r:record[n:t]{self.'A['self];'R}; <J['r]> >- 'C['r; field[n:t]{'r}]}

interactive recordEliminationL1  'H :
   [main] sequent{ <H>; r:'R; x:'A['r]; <J>  >- 'C[rcrd[n:t]{'x;'r}]} -->
   sequent{ <H>; r:record[n:t]{self.'A['self];'R}; <J> >- 'C['r]}

interactive recordEliminationL 'H :
   [ort] sequent{ <H>; r:record[n:t]{self.'A['self];'R}; <J['r]>; rr:'R; x:'A['rr]
                                                                >- record_ort[n:t]{'x;'R} } -->
   [main] sequent{ <H>; r:'R; x:'A['r]; <J[rcrd[n:t]{'x;'r}]> >- 'C[rcrd[n:t]{'x;'r}]} -->
   sequent{ <H>; r:record[n:t]{self.'A['self];'R}; <J['r]> >- 'C['r]}

(* Right-assotiated Records *)

interactive recordEliminationR2 {| elim[] |} 'H bind{rr,z.'C['rr;'z]}:
   [main] sequent{ <H>; r:record[n:t]{'A;x.'R['x]}; <J['r]>; x:'A; rr:'R['x] >- 'C['rr;'x]} -->
   sequent{ <H>; r:record[n:t]{'A;x.'R['x]}; <J['r]> >- 'C['r; field[n:t]{'r}]}

interactive recordEliminationR1 'H :
   [main] sequent{ <H>; x:'A; r:'R['x]; <J>  >- 'C[rcrd[n:t]{'x;'r}]} -->
   sequent{ <H>; r:record[n:t]{'A;x.'R['x]}; <J> >- 'C['r]}

interactive recordEliminationR 'H :
   [ort] sequent{ <H>; r:record[n:t]{'A;x.'R['x]}; <J['r]>; x:'A; 'R['x] >- record_ort[n:t]{'x;'R['x]} } -->
   [main] sequent{ <H>; x:'A; r:'R['x]; <J[rcrd[n:t]{'x;'r}]> >- 'C[rcrd[n:t]{'x;'r}]} -->
   sequent{ <H>; r:record[n:t]{'A;x.'R['x]}; <J['r]> >- 'C['r]}

(* Independent Records *)

interactive recordEliminationI2  'H :
   [main] sequent{ <H>; r:record[n:t]{'A;'R}; <J['r]>; x:'A; rr:'R >- 'C['rr]} -->
   sequent{ <H>; r:record[n:t]{'A;'R}; <J['r]> >- 'C['r]}

interactive recordEliminationI1  'H :
   [main] sequent{ <H>; x:'A; r:'R; <J>  >- 'C[rcrd[n:t]{'x;'r}]} -->
   sequent{ <H>; r:record[n:t]{'A;'R}; <J> >- 'C['r]}

interactive recordEliminationI  'H :
   [ort] sequent{ <H>; r:record[n:t]{'A;'R}; <J['r]>; x:'A; rr:'R >- record_ort[n:t]{'x;'R} } -->
   [main] sequent{ <H>; x:'A; r:'R; <J[rcrd[n:t]{'x;'r}]> >- 'C[rcrd[n:t]{'x;'r}]} -->
   sequent{ <H>; r:record[n:t]{'A;'R}; <J['r]> >- 'C['r]}

doc <:doc< @docoff >>

let recordS_elim = argfunT (fun n p ->
 let n = Sequent.get_pos_hyp_num p n in
    (recordEliminationS n)
    thenT
      (record_reduceT thenMT tryT (thinT (n+1))))

let recordL_elim = argfunT (fun n p ->
 let n = Sequent.get_pos_hyp_num p n in
    (recordEliminationL1 n orelseT recordEliminationL n)
    thenT
       ifLabT "ort"
                (tryT (dT 0 thenWT tryT (typeAssertT thenT nthHypT (-2))))
       (*else*) (record_reduceT thenMT tryT (dT n)))

let recordR_elim = argfunT (fun n p ->
 let n = Sequent.get_pos_hyp_num p n in
    (recordEliminationR1 n orelseT recordEliminationR n)
    thenT
       ifLabT "ort"
                (tryT (dT 0 thenWT tryT (typeAssertT thenT nthHypT (-1))))
       (*else*) (record_reduceT thenMT tryT (dT (n+1))))

let recordI_elim = argfunT (fun n p ->
 let n = Sequent.get_pos_hyp_num p n in
    (recordEliminationI1 n orelseT recordEliminationI n)
    thenT
       ifLabT "ort"
                (tryT (dT 0 thenWT tryT (typeAssertT thenT nthHypT (-1))))
       (*else*) (record_reduceT thenMT tryT (dT (n+1))))

let resource elim += [
   (<<record[m:t]{'A}>>,recordS_elim);
   (<<record[m:t]{'A;'R}>>,recordI_elim);
   (<<record[m:t]{'A;a.'R['a]}>>,recordR_elim);
   (<<record[m:t]{self.'A['self];'R}>>,recordL_elim)
]

(*** Orthogonality ***)
doc <:doc< @doc{@modsubsection{Orthogonality}} >>

interactive functionOrtDinter {| intro[] |} :
   [wf] sequent{ <H> >- "type"{bisect{'A;a.'B['a]}} } -->
   [main] sequent{ <H>; a:'A; b:'B['a] >- function_ort{x.'f['x];'A} } -->
   [main] sequent{ <H>; a:'A; b:'B['a] >- function_ort{x.'f['x];'B['a]} } -->
   sequent{ <H> >-  function_ort{x.'f['x]; bisect{'A;a.'B['a]}} }

interactive recordOrtIntro0 {| intro[] |} :
   sequent{ <H>  >- record_ort[n:t]{'a;record} }

interactive recordOrtIntroT {| intro[] |} :
   sequent{ <H>  >- record_ort[n:t]{'a;top} }

interactive recordOrtIntroTop {| intro[] |} :
   [wf] sequent{ <H>  >- "type"{tsquash{'A}} } -->
   sequent{ <H>  >- record_ort[n:t]{'a;tsquash{'A}} }

interactive recordOrtIntroS1 :
   [wf] sequent{ <H> >- "type"{record[m:t]{'A}} } -->
   [main] sequent{ <H> >-  label[n:t]<>label[m:t] in label } -->
   sequent{ <H> >- record_ort[n:t]{'a;record[m:t]{'A}} }

interactive recordOrtIntroS2 :
   [wf] sequent{ <H> >- "type"{record[n:t]{'A}} } -->
   [main] sequent{ <H>; x:'A >- 'x='a in 'A } -->
   sequent{ <H> >- record_ort[n:t]{'a;record[n:t]{'A}} }

let recordOrtIntroST =
   recordOrtIntroS2 orelseT recordOrtIntroS1

let resource intro += (<<record_ort[n:t]{'a;record[m:t]{'A}}>>,wrap_intro recordOrtIntroST)

interactive recordOrtIntroL :
   [wf] sequent{ <H> >- "type"{record[m:t]{self.'A['self];'R}} } -->
   [main] sequent{ <H>; r:'R; x:'A['r] >- record_ort[n:t]{'a;'R}}  -->
   [main] sequent{ <H>; r:'R; x:'A['r] >- record_ort[n:t]{'a;record[m:t]{'A['r]}}}  -->
   sequent{ <H> >- record_ort[n:t]{'a;record[m:t]{self.'A['self];'R}} }

let recordOrtIntroLT =
   recordOrtIntroL thenLT
      [idT;
       tryT (dT 0 thenWT tryT (typeAssertT thenT nthHypT (-2)));
       rwh record_reduce 0 thenT tryT recordOrtIntroST thenWT tryT (dT 0 thenT typeAssertT thenT nthHypT (-1));
      ]

let resource intro += (<<record_ort[n:t]{'a;record[m:t]{self.'A['self];'R}}>>,wrap_intro recordOrtIntroLT)

interactive recordOrtIntroR :
   [wf] sequent{ <H> >- "type"{record[m:t]{'A;x.'R['x]}} } -->
   [main] sequent{ <H>; x:'A; r:'R['x] >- record_ort[n:t]{'a;'R['x]} } -->
   [main] sequent{ <H>; x:'A; r:'R['x] >- record_ort[n:t]{'a;record[m:t]{'A}}}  -->
   sequent{ <H> >- record_ort[n:t]{'a;record[m:t]{'A;x.'R['x]}} }

let recordOrtIntroRT =
   recordOrtIntroR thenLT
      [idT;
       tryT (dT 0 thenWT tryT (typeAssertT thenT nthHypT (-1)));
       tryT recordOrtIntroST thenWT tryT (dT 0 thenT typeAssertT thenT nthHypT (-2));
      ]

let resource intro += (<<record_ort[n:t]{'a;record[m:t]{'A;x.'R['x]}}>>,wrap_intro recordOrtIntroRT)

interactive recordOrtIntroI :
   [wf] sequent{ <H> >- "type"{record[m:t]{'A;'R}} } -->
   [main] sequent{ <H>; x:'A; r:'R >- record_ort[n:t]{'a;'R} } -->
   [main] sequent{ <H>; x:'A; r:'R >- record_ort[n:t]{'a;record[m:t]{'A}}} -->
   sequent{ <H> >- record_ort[n:t]{'a;record[m:t]{'A;'R}} }

let recordOrtIntroIT =
   recordOrtIntroI thenLT
      [idT;
       tryT (dT 0 thenWT tryT (typeAssertT thenT nthHypT (-1)));
       tryT recordOrtIntroST thenWT tryT (dT 0 thenT typeAssertT thenT nthHypT (-2));
      ]

let resource intro += (<<record_ort[n:t]{'a;record[m:t]{'A;'R}}>>,wrap_intro recordOrtIntroIT)

interactive recordOrtSetIntro {| intro [] |} :
	[wf] sequent { <H>;  r: 'T >- 'P['r] Type } -->
	[wf] sequent { <H> >- { r: 'T | 'P['r] } Type } -->
	sequent { <H> >- record_ort[n:t]{ 'R; 'T} } -->
	sequent { <H> >- record_ort[n:t]{ 'R; { r: 'T | 'P['r] } } }

interactive recordOrtBisectIntro {| intro [] |} :
	[wf] sequent { <H> >- 'A Type } -->
	[wf] sequent { <H> >- 'B Type } -->
	sequent { <H> >- record_ort[n:t]{ 'R; 'A} } -->
	sequent { <H> >- record_ort[n:t]{ 'R; 'B} } -->
	sequent { <H> >- record_ort[n:t]{ 'R; bisect{ 'A; 'B} } }

(******************)
(*  Tactics       *)
(******************)

doc <:doc< @docoff >>

(*
let elim0 rule p n =
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
            let field = mk_rcrd_term x
            let concl = (Sequent.concl p) in
            let concl1 = var_subst concl r.x

            mk_bind2_term z (var_subst ) a z)
*)

(*** Ortogonality ***)
(*
let recordOrtIntro0T = recordOrtIntro0

let recordOrtIntroST p =
   let x= maybe_new_vars1 p "x" in
      ( (recordOrtIntroSM x orelseT recordOrtIntroS x)
        thenMT  rw reduce_eq_label 0
        thenWT tryT (typeAssertT thenT trivialT)
        thenT tryT (completeT (dT 0))
      ) p

let resource intro += (<<record_ort[n:t]{'a;record[m:t]{'A}}>>, wrap_intro recordOrtIntroST)

let recordOrtIntroT p =
   let x= maybe_new_vars1 p "x" in
      ((recordOrtIntroM x orelseT recordOrtIntro x) thenMT  rw reduce_eq_label 0) p

let repeatRecordOrtIntroT = (untilFailT recordOrtIntroT) thenT tryT (recordOrtIntroST orelseT recordOrtIntro0T)

let resource intro += (<<record_ort[n:t]{'a;record[m:t]{'A;'R}}>>, wrap_intro repeatRecordOrtIntroT)

*)
(*** Elimination ***)
(*
let repeatRecEl tac n p =
   dT n thenMT dT (n+1)
      tac n thenMT tryT (tac (n+1))
          orelseT recordEliminationS j k x) p
*)
(*
let rec repeatRecordEliminationT n p =
   let n = Sequent.get_pos_hyp_num p n in
      ((recordElimination j k
           thenMT tryT (repeatRecordEliminationT (n+1)))
          orelseT recordEliminationS n x) p

let recordDefEliminationT n = repeatRecordEliminationT n thenAT tryT repeatRecordOrtIntroT

let recordEliminationT n p =
   let n = Sequent.get_pos_hyp_num p n in
   try
      let sel = get_sel_arg p in
         if sel = 0 then recordElimination2 n p else
            (recordElimination1 n orelse recordElimination n) p
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

let t = <<'alpha>>

(*************
 * Subtyping
 *************)

interactive recordLSubtype {| intro [] |} :
	[wf] sequent { <H> >- 'S Type } -->
	[wf] sequent { <H>; x: 'S >- 'A['x] Type } -->
	sequent { <H> >- record[n:t]{r.'A['r];'S} subtype 'S }

interactive recordRSubtype {| intro [] |} :
	[wf] sequent { <H> >- 'S Type } -->
	[wf] sequent { <H>; x: 'S >- 'A['x] Type } -->
	sequent { <H> >- record[n:t]{'S; r.'A['r]} subtype record[n:t]{'S} }

interactive recordSubtype1 {| intro [] |} :
	[wf] sequent { <H> >- 'R Type } -->
	[wf] sequent { <H> >- 'S Type } -->
	sequent { <H> >- record[n:t]{'R;'S} subtype record[n:t]{'R} }

interactive recordSubtype2 {| intro [] |} :
	[wf] sequent { <H> >- 'R Type } -->
	[wf] sequent { <H> >- 'S Type } -->
	sequent { <H> >- record[n:t]{'R;'S} subtype 'S }

(******************)
(*  Display Forms *)
(******************)

declare subrecord{'A}
declare self{'self}

declare self[n:t]{'x}

(*
dform self_df : except_mode [src] ::  self{'self} = `""
*)

dform self_df : except_mode [src] ::  self{'self} = 'self

dform field_df : except_mode [src] :: field[t:t]{'r} = field{'r;label[t:t]}

dform field_self  : except_mode [src] ::  field[t:t]{self{'self}} = label[t:t]

dform self_lab_df : except_mode [src] ::  self[n:t]{'x} = field[n:t]{self{'x}}

declare "{"
declare "}"
declare ";"
declare "|"

dform open_record_df : "{" = szone pushm  `"{" pushm
dform close_record_df : "}" = popm `"}" popm ezone
dform separator_record_df : ";" = `";" hspace
dform separator_record_df : "|" = `" |" hspace

dform subrecord_df : except_mode [src] :: subrecord{'r} = 'r

dform subrcrdS_df : except_mode [src] :: subrecord{rcrd[n:t]{'a}}
   = declaration{label[n:t];'a}

dform subrecordS_df : except_mode [src] :: subrecord{record[n:t]{'a}}
   = label[n:t] `":" slot{'a}

dform subrcrd_df : except_mode [src] :: subrecord{rcrd[n:t]{'a;'r}}
   =  subrecord{'r} ";" subrecord{rcrd[n:t]{'a}}

dform subrcrdS2_df : except_mode [src] :: subrecord{rcrd[n:t]{'a;rcrd}}
   =  subrecord{rcrd[n:t]{'a}}

dform subrecordI_df : except_mode [src] :: subrecord{record[n:t]{'a;'r}}
   = subrecord{record[n:t]{'a}} ";" subrecord{'r}

dform subrecordL_df : except_mode [src] :: subrecord{record[n:t]{self.'a['self];'r}}
   = subrecord{'r} ";" subrecord{record[n:t]{'a[self{'self}]}}

dform subrecordR_df : except_mode [src] :: subrecord{record[n:t]{'a;x.'r['x]}}
   = subrecord{record[n:t]{'a}} ";" subrecord{'r[self[n:t]{'x}]}

dform set_record_df : except_mode [src] :: subrecord{{self: 'A | 'P['self]}}
   =  'self `":" slot{'A} "|" 'P[self{'self}]

dform set_record_df : except_mode [src] :: subrecord{{self:{self2:'a | 'P2['self2]} | 'P['self]}}
   =  subrecord{{self:'a | 'P2['self]}} "|" 'P[self{'self}]

dform set_record_df : except_mode [src] :: subrecord{{self: record[n:t]{self2.'a['self2];'r} | 'P['self]}}
   =  subrecord{record[n:t]{self2.'a['self2];'r}} "|" 'P[self{'self2}]

dform rcrdS_df : except_mode [src] :: rcrd[n:t]{'a}
   = "{" subrecord{rcrd[n:t]{'a}} "}"

dform rcrd_df : except_mode [src] :: rcrd[n:t]{'a;'r}
   =  "{" subrecord{rcrd[n:t]{'a;'r}} "}"

dform recordS_df : except_mode [src] :: record[n:t]{'a}
   =  "{" subrecord{record[n:t]{'a}} "}"

dform recordI_df : except_mode [src] :: record[n:t]{'a;'r}
   =  "{" subrecord{record[n:t]{'a;'r}} "}"

dform recordR_df : except_mode [src] :: record[n:t]{self.'a['self];'r}
   =  "{" subrecord{record[n:t]{self.'a['self];'r}} "}"

dform recordL_df : except_mode [src] :: record[n:t]{'a;x.'r['x]}
   =  "{" subrecord{record[n:t]{'a;x.'r['x]}} "}"

dform set_record_df : except_mode [src] ::  ({self:'a | 'P['self]})
   =  "{" subrecord{{self:'a | 'P['self]}} "}"

dform functionOrt_df : except_mode [src] :: function_ort{x.'f['x];'R}
     =  slot{'f[math_bf{cdot}]} perp slot{'R}

dform recordOrt_df : except_mode [src] :: record_ort[n:t]{'a;'R}
     =   rcrd[n:t]{'a} perp 'R

(* TODO List:
 *  - I want to eliminate types like {x:A; R_1} isect R_2.
      One way is to write an elimination rule for any such type. But there are too many of them! (4 records*2 intersections * 2 orders = 16 types!)
      There are should be an easier way!
 *  - After that associative rule should be proved very easy.
    - Sets and records.
    - Elimination (and inrto) tactics:
        : there should be an easy way to make only one elimination (intro)
        : dT (-n) does not work ( next(-n) = -n , and next(-n) = -(n+1) )
    - Renaming labels
   - intro should give only one wf-subgoal. E.g. {x=a;y=b;z=c} in {x:A;y:B[x]; z:C[x,y]} sould produce only wf subgal: {x:A;y:B[x]; z:C[x,y]} Type
     (not that x:A |- {y:B[x]; z:C[x,y]} Type ). The same is for sets.
     There should be a general approach to deal with it.
   - make grammar understand {x:A;y:B;}
   - update record_exm

 BUGS :
   - currently display forms for self implementes in hacker way.
   Also dforms for sets: {x:A | B[x]} x is treated as self sometimes works strange,
   e.g. <<{y:{x:{aaa:'r; bbb:'r['self]} | 'B['x]} | 'C['y]}>> is displayed as {aaa:r; bbb:r[self] | B[self] | C[y]}
   Not all cases of sets and records are implemented. Intersection and records?
#

*)
