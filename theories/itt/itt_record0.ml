include Itt_theory
include Itt_record_label0
include Itt_struct3
include Itt_inv_typing

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
open Itt_inv_typing

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
let resource reduce +=
   [<< record{zero;'A} >>, baseRecord;
    << record{next{'n};'A} >>,stepRecord_rw]
(*! *)

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

(*! @docoff *)
let resource reduce +=
   [<< rcrd{zero;'a; 'r} >>, baseRcrd;
    << rcrd{next{'n};'a; 'r} >>, stepRcrd_rw;
   ]

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
let resource reduce +=
   [<< field{'A;zero} >>, baseField;
    << field{'r;next{'n}} >>, stepField_rw]
(*! *)

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

interactive record_elim1 'H 'n :
   [wf] sequent[squash]{'H >- 'n IN label } -->
   sequent['ext]{'H >- record{'n;'A} } -->
   sequent['ext]  {'H >- "type"{'A} }

interactive recordTypeElimination{| elim_resource [ThinOption thinT]  |} 'H 'J 'v:
   sequent[squash]{'H; u:"type"{record{'n;'A}}; 'J['u] >- 'n IN label} -->
   sequent['ext]  {'H; u:"type"{record{'n;'A}}; v:"type"{'A}; 'J['u] >- 'C['u] } -->
   sequent['ext]  {'H; u:"type"{record{'n;'A}}; 'J['u] >- 'C['u] }


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
   sequent['ext]  {'H >- rcrd{'n; field{'r;'n}; 'r} ~ 'r }

interactive_rw record_eta_rw  :
   ('n IN label ) -->
   ('r IN record{'n;top} ) -->
   rcrd{'n; field{'r;'n}; 'r} <--> 'r


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



(******************)
(*  Display Forms *)
(******************)

(*! @docoff *)



dform emptyRecord_df : except_mode [src] :: record = `"{}"

dform emptyRcrd_df : except_mode [src] :: rcrd = `"{}"



dform field_df : except_mode [src] :: field{'r;'n} =  slot{'r} `"." slot{'n}



dform rcrd_df : except_mode [src] :: rcrd{'n;'a; 'r} = `"{" slot{'n} `"=" slot{'a} `";" slot{'r} `"}"


dform recordS_df : except_mode [src] :: record{'n;'A} = `"{" slot{'n} `":" slot{'A} `"}"












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

