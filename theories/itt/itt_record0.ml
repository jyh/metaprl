
include Itt_theory
include Itt_record_label0
include Itt_struct3

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

open Itt_equal
open Itt_subtype
open Itt_struct
open Itt_record_label0
open Itt_struct3

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_record0%t"


(******************)
(*  Definitions   *)
(******************)

(*! *)

(*** Empty Record Type ***)

define unfoldEmptyRecord : record <--> top

(*** Single Record Type ***)

define unfoldRecordS : record{'n;'A} <--> ind_lab{'n; ('A * record); l . top * 'l}

interactive_rw baseRecord : record{zero;'A} <--> ('A * record)

interactive stepRecord {| intro_resource[] |}'H :
   sequent[squash]  {'H >- 'n IN label} -->
   sequent['ext] {'H >- record{next{'n};'A} ~ top * record{'n;'A} }

interactive_rw stepRecord_rw  :
   ('n IN label) -->
   record{.next{'n};'A} <--> (top * record{'n;'A})

(*! @docoff *)
let reduce_info =
   [<< record{zero;'A} >>, baseRecord;
    << record{next{'n};'A} >>,stepRecord_rw]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info
(*! *)


(*** Recursive Record Type ***)

define unfoldRecord : record{'n;'A;'R} <--> bisect{record{'n;'A};'R}

let foldRecord = makeFoldC  <<record{'n;'A;'R}>> unfoldRecord

(*** records ***)

declare rcrd

define unfoldRcrd : rcrd{'n;'a; 'r} <-->
   ind_lab{'n; lambda{r.('a, snd{'r})}; l.lambda{r.(fst{'r},'l snd{'r})}} 'r

interactive_rw baseRcrd : rcrd{zero;'a; 'r} <--> ('a, snd{'r})

interactive stepRcrd {| intro_resource [] |} 'H :
   sequent[squash]  {'H >- 'n IN label} -->
   sequent['ext] {'H >- rcrd{next{'n};'a; 'r} ~ (fst{'r},rcrd{'n;'a;snd{'r}}) }

interactive_rw stepRcrd_rw  :
   ('n IN label) -->
   rcrd{.next{'n};'a; 'r} <--> (fst{'r},rcrd{'n;'a;snd{'r}})

define unfoldRcrdS : rcrd{'n;'a} <--> rcrd{'n; 'a; rcrd}

(*! @docoff *)
let reduce_info =
   [<< rcrd{zero;'a; 'r} >>, baseRcrd;
    << rcrd{next{'n};'a; 'r} >>, stepRcrd_rw;
    << rcrd{'n;'a} >>, unfoldRcrdS
   ]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info

let intro_resource =
   Mp_resource.improve intro_resource (<<rcrd{'n;'a} = 'r in 'R>>, (rwh unfoldRcrdS 0 thenT dT 0))
let intro_resource =
   Mp_resource.improve intro_resource (<<'r = rcrd{'n;'a} in 'R>>, (rwh unfoldRcrdS 0 thenT dT 0))
(*! *)


(*** Field ***)

define unfoldField : field{'r;'n} <--> ind_lab{'n; lambda{r. fst{'r}};  l .lambda{r.'l snd{'r}}} 'r

interactive_rw baseField : field{'r;zero} <--> fst{'r}

interactive stepField {| intro_resource [] |}'H :
   sequent[squash]  {'H >- 'n IN label} -->
   sequent['ext] {'H >- field{'r;next{'n}} ~ (field{snd{'r};'n}) }

interactive_rw stepField_rw  :
   ('n IN label) -->
   field{'r;next{'n}} <--> (field{snd{'r};'n})

(*! @docoff *)
let reduce_info =
   [<< field{'A;zero} >>, baseField;
    << field{'r;next{'n}} >>, stepField_rw]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info
(*! *)

(*** RecordOrt ***)

define unfoldRecordOrt : record_ort{'n;'a;'R} <--> (all r:'R. (rcrd{'n;'a;'r} IN 'R))

(******************)
(*   Rules        *)
(******************)

(*** Typing ***)

interactive emptyRecordType {| intro_resource [] |} 'H :
   sequent['ext]  {'H >- "type"{record} }

interactive recordType {| intro_resource [] |} 'H :
   sequent[squash]{'H >- "type"{'A} } -->
   sequent[squash]{'H >- 'n IN label} -->
   sequent['ext]  {'H >- "type"{record{'n;'A}} }

interactive recordType2 {| intro_resource [] |} 'H :
   [wf] sequent[squash]{'H >- 'n IN label} -->
   sequent[squash]{'H >- "type"{'A} } -->
   sequent[squash]{'H >- "type"{'R} } -->
   sequent['ext]  {'H >- "type"{record{'n;'A;'R}} }

interactive record_elim1 'H 'n :
   [wf] sequent[squash]{'H >- 'n IN label } -->
   sequent['ext]{'H >- record{'n;'A} } -->
   sequent['ext]  {'H >- "type"{'A} }

(*** Introductions ***)

interactive emptyRecordIntro {| intro_resource[] |} 'H :
   sequent['ext]  {'H >-'r_1 = 'r_2 in record }

interactive recordEqualS1  {| intro_resource[SelectOption 1] |} 'H:
   [equality] sequent[squash]{'H >- 'n1='m in label } -->
   [equality] sequent[squash]{'H >- 'n2='m in label } -->
   sequent[squash]{'H >- 'a1 ='a2 in 'A } -->
   sequent['ext]  {'H >- rcrd{'n1;'a1;'r1}=rcrd{'n2;'a2;'r2} in record{'m;'A} }

interactive recordIntroS1  {| intro_resource[SelectOption 1] |} 'H:
   [equality] sequent[squash]{'H >- 'n='m in label } -->
   sequent[squash]{'H >- 'a IN 'A } -->
   sequent['ext]  {'H >- rcrd{'n;'a;'r} IN record{'m;'A} }

interactive recordIntroS2  {| intro_resource[SelectOption 2] |} 'H:
   [wf] sequent[squash]{'H >- 'n IN label } -->
   [wf] sequent[squash]{'H >- 'm IN label } -->
   [equality] sequent[squash]{'H >- not{.'n ='m in label} } -->
   sequent[squash]{'H >- 'r IN record{'m;'A} } -->
   sequent['ext]  {'H >- rcrd{'n;'a;'r} IN record{'m;'A} }

interactive recordEqualS2  {| intro_resource[SelectOption 2] |} 'H:
   [wf] sequent[squash]{'H >- 'n IN label } -->
   [wf] sequent[squash]{'H >- 'm IN label } -->
   [equality] sequent[squash]{'H >- not{.'n='m in label} } -->
   sequent[squash]{'H >- 'r1='r2 in record{'m;'A} } -->
   sequent['ext]  {'H >- rcrd{'n;'a;'r1}='r2 in record{'m;'A} }

interactive recordEqualS3  {| intro_resource[SelectOption 3] |} 'H:
   [wf] sequent[squash]{'H >- 'n IN label } -->
   [wf] sequent[squash]{'H >- 'm IN label } -->
   [equality] sequent[squash]{'H >- not{.'n='m in label} } -->
   sequent[squash]{'H >- 'r1='r2 in record{'m;'A} } -->
   sequent['ext]  {'H >- 'r1=rcrd{'n;'a;'r2} in record{'m;'A} }

interactive recordIntro  {| intro_resource[] |} 'H:
   sequent[squash]{'H >- 'r = 's in 'R } -->
   sequent[squash]{'H >- 'r = 's in record{'n;'A} } -->
   sequent['ext]  {'H >- 'r = 's in record{'n;'A;'R} }

interactive recordIntro0  {| intro_resource[SelectOption 0] |} 'H:
   [wf] sequent[squash]{'H >- 'n IN label } -->
   sequent[squash]{'H >- 'r IN 'R } -->
   [ort] sequent[squash]{'H; u:'R >- record_ort{'n;'a;'R} } -->
   sequent['ext]  {'H >- rcrd{'n;'a;'r} IN 'R }

(*** Reductions ***)

interactive record_beta1 {| intro_resource[] |} 'H:
   [equality] sequent[squash]{'H >- 'n ='m in label } -->
   sequent['ext]  {'H >- field{rcrd{'n; 'a; 'r};'m} ~ 'a }

interactive record_beta2 {| intro_resource[] |} 'H:
   [wf] sequent[squash]{'H >- 'n IN label } -->
   [wf] sequent[squash]{'H >- 'm IN label } -->
   [equality] sequent[squash]{'H >- not{.'n ='m in label} } -->
   sequent['ext]  {'H >- field{rcrd{'n; 'a; 'r};'m} ~ field{'r;'m} }

interactive record_beta12  {| intro_resource[] |} 'H:
   [wf] sequent[squash]{'H >- 'n IN label } -->
   [wf] sequent[squash]{'H >- 'm IN label } -->
   sequent['ext]  {'H >- field{rcrd{'n; 'a; 'r};'m} ~ ifthenelse{eq_label{'n;'m};'a;field{'r;'m}} }


interactive record_eta  {| intro_resource[] |}'H 'A:
   [wf] sequent[squash]{'H >- 'n IN label } -->
   [wf] sequent[squash]{'H >- 'r IN record{'n;'A} } -->
   sequent['ext]  {'H >- 'r ~ rcrd{'n; field{'r;'n}; 'r} }


interactive record_cover  {| intro_resource[] |} 'H:
   [equality] sequent[squash]{'H >- 'n ='m in label } -->
   sequent['ext]  {'H >- rcrd{'n; 'a; rcrd{'m; 'b; 'r}} ~  rcrd{'n; 'a; 'r} }

interactive record_exchange {| intro_resource[] |} 'H:
   [wf] sequent[squash]{'H >- 'n IN label } -->
   [wf] sequent[squash]{'H >- 'm IN label } -->
   [equality] sequent[squash]{'H >- not{.'n='m in label} } -->
   sequent['ext]  {'H >- rcrd{'n; 'a; rcrd{'m; 'b; 'r}} ~  rcrd{'m; 'b; rcrd{'n; 'a; 'r}} }


(*** Eliminations ***)

interactive field_member {| intro_resource[] |} 'H:
   [wf] sequent[squash]{'H >- 'n IN label } -->
   sequent[squash]{'H >- 'r IN record{'n;'A} } -->
   sequent['ext]  {'H >- field{'r;'n} IN 'A }

interactive recordEliminationS {| elim_resource[] |} 'H 'J 'x:
   [wf] sequent[squash]{'H; r:record{'n;'A}; 'J['r] >- 'n IN label } -->
   sequent['ext]  {'H; x:'A; r:record; 'J[rcrd{'n;'x;'r}] >- 'C[rcrd{'n;'x;'r}]} -->
   sequent['ext]  {'H; r:record{'n;'A}; 'J['r] >- 'C['r]}


interactive recordElimination  'H 'J :
   [ort] sequent[squash]{'H; r:record{'n;'A;'R}; 'J['r]; x:'A; rr:'R >- record_ort{'n;'x;'R} } -->
   [wf]  sequent[squash]{'H; r:record{'n;'A;'R}; 'J['r] >- 'n IN label } -->
   sequent['ext]  {'H; x:'A; r:'R; 'J[rcrd{'n;'x;'r}] >- 'C[rcrd{'n;'x;'r}]} -->
   sequent['ext]  {'H; r:record{'n;'A;'R}; 'J['r] >- 'C['r]}

interactive recordElimination0  'H 'J :
   [wf]  sequent[squash]{'H; r:record{'n;'A;'R}; 'J['r] >- 'n IN label } -->
   sequent['ext]  {'H; r:record{'n;'A;'R}; 'J['r]; x:'A; r':'R >- 'C['r]} -->
   sequent['ext]  {'H; r:record{'n;'A;'R}; 'J['r] >- 'C['r]}

interactive recordElimination1  'H 'J :
   [wf]  sequent[squash]{'H; r:record{'n;'A;'R}; 'J['r] >- 'n IN label } -->
   sequent['ext]  {'H; r:record{'n;'A;'R}; 'J['r]; x:'A; rr:'R >- 'C[rcrd{'n;'x;'rr}]} -->
   sequent['ext]  {'H; r:record{'n;'A;'R}; 'J['r] >- 'C['r]}

interactive recordElimination2  'H 'J :
   [wf]  sequent[squash]{'H; r:record{'n;'A;'R}; 'J['r] >- 'n IN label } -->
   sequent['ext]  {'H; r:record{'n;'A;'R}; 'J['r]; x:'A; rr:'R >- 'C['rr]} -->
   sequent['ext]  {'H; r:record{'n;'A;'R}; 'J['r] >- 'C['r]}

let recordEliminationT n p =
   let j, k = Sequent.hyp_indices p n in
   try
      let sel = get_sel_arg p in
         if sel = 0 then recordElimination0 j k p else
         if sel = 1 then recordElimination1 j k p else
         if sel = 2 then recordElimination2 j k p else
           recordElimination j k p
   with
         RefineError _ -> recordElimination j k p

let elim_resource = Mp_resource.improve elim_resource (<<record{'n;'A;'R}>>, recordEliminationT)

(*** Orthogonality ***)

interactive recordOrtIntro0 {| intro_resource[] |} 'H  :
   sequent['ext]  {'H  >- record_ort{'n;'a;record} }

interactive recordOrtIntroS1 {| intro_resource[SelectOption 1] |} 'H  'x  :
   [wf] sequent[squash]{'H >- 'n IN label } -->
   [wf] sequent[squash]{'H >- 'm IN label } -->
   sequent[squash]  {'H; x:'A >- 'a IN 'A } -->
   sequent['ext]  {'H; r:record{'m;'A}  >- record_ort{'n;'a;record{'m;'A}} }

interactive recordOrtIntroS2 {| intro_resource[SelectOption 2] |} 'H  'x  :
   [wf] sequent[squash]{'H >- 'n IN label } -->
   [wf] sequent[squash]{'H >- 'm IN label } -->
   [equality] sequent[squash]{'H; r:record{'m;'A} >- not{.'n = 'm in label} } -->
   sequent['ext]  {'H; r:record{'m;'A}  >- record_ort{'n;'a;record{'m;'A}} }

interactive recordOrtIntro1 {| intro_resource[SelectOption 1] |} 'H  'x  :
   [wf] sequent[squash]{'H >- 'n IN label } -->
   [wf] sequent[squash]{'H >- 'm IN label } -->
   sequent[squash]  {'H; x:'A; r:'R >- 'a IN 'A } -->
   [ort] sequent[squash]  {'H; x:'A; r:'R >- record_ort{'n;'a;'R} } -->
   sequent['ext]  {'H; r:record{'m;'A;'R}  >- record_ort{'n;'a;record{'m;'A;'R}} }

interactive recordOrtIntro2 {| intro_resource[SelectOption 2] |} 'H  'x  :
   [wf] sequent[squash]{'H >- 'n IN label } -->
   [wf] sequent[squash]{'H >- 'm IN label } -->
   [equality] sequent[squash]{'H; r:record{'m;'A;'R} >- not{.'n = 'm in label} } -->
   [ort] sequent[squash]  {'H; x:'A; r:'R >- record_ort{'n;'a;'R} } -->
   sequent['ext]  {'H; r:record{'m;'A;'R}  >- record_ort{'n;'a;record{'m;'A;'R}} }




(******************)
(*  Display Forms *)
(******************)

(*! @docoff *)



dform emptyRecord_df : except_mode [src] :: record = `"{}"

dform emptyRcrd_df : except_mode [src] :: rcrd = `"{}"



dform field_df : except_mode [src] :: field{'r;'n} =  slot{'r} `"." slot{'n}


dform rcrdS_df : except_mode [src] :: rcrd{'n;'a} = `"{" slot{'n} `"=" slot{'a} `"}"

dform rcrd_df : except_mode [src] :: rcrd{'n;'a; 'r} = `"{" slot{'n} `"=" slot{'a} `";" slot{'r} `"}"


dform recordS_df : except_mode [src] :: record{'n;'A} = `"{" slot{'n} `":" slot{'A} `"}"

dform record_df : except_mode [src] :: record{'n;'A;'R} = `"{" slot{'n} `":" slot{'A} `";" slot{'R} `"}"

dform recordOrt_df : except_mode [src] :: record_ort{'n;'a;'R} =  `"{" slot{'n} `"=" slot{'a} `"}_|_" slot{'R}










interactive test :
   sequent['ext]  { >-  'C}

(*
let doubleInductionT =
 letT <<'rr='r in record>> thenAT autoT thenT thinT (-1) thenT moveToConclT 2
 thenT genAssumT [1;2;3] thenLT
    [repeatMForT 2 (dT 0 thenMT dT (-1) thenMT rwh reduceC 0) thenT autoT;
     assumT 3 thenT dT (-1) thenT autoT
    ]
*)

