extends Itt_record_label0
extends Itt_struct3
extends Itt_inv_typing

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
open Dtactic
open Top_conversionals

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

doc <:doc< >>

(*** Empty Record Type ***)

define unfoldEmptyRecord : record <--> top

(*** Single Record Type ***)

define unfoldRecordS : record{'n;'A} <--> ind_lab{'n; ('A * record); l . top * 'l}

interactive_rw baseRecord {| reduce |} : record{zero;'A} <--> ('A * record)

interactive stepRecord {| intro[] |} :
   sequent{ <H> >- 'n in label} -->
   sequent{ <H> >- record{next{'n};'A} ~ top * record{'n;'A} }

interactive_rw stepRecord_rw {| reduce |} :
   ('n in label) -->
   record{.next{'n};'A} <--> (top * record{'n;'A})

(*** records ***)

declare rcrd

define unfoldRcrd : rcrd{'n;'a; 'r} <-->
   ind_lab{'n; lambda{r.('a, snd{'r})}; l.lambda{r.(fst{'r},'l snd{'r})}} 'r

interactive_rw baseRcrd {| reduce |} : rcrd{zero;'a; 'r} <--> ('a, snd{'r})

interactive stepRcrd {| intro [] |} :
   sequent{ <H> >- 'n in label} -->
   sequent{ <H> >- rcrd{next{'n};'a; 'r} ~ (fst{'r},rcrd{'n;'a;snd{'r}}) }

interactive_rw stepRcrd_rw {| reduce |} :
   ('n in label) -->
   rcrd{.next{'n};'a; 'r} <--> (fst{'r},rcrd{'n;'a;snd{'r}})

(*** Field ***)

define unfoldField : field{'r;'n} <--> ind_lab{'n; lambda{r. fst{'r}};  l .lambda{r.'l snd{'r}}} 'r

interactive_rw baseField {| reduce |} : field{'r;zero} <--> fst{'r}

interactive stepField {| intro [] |} :
   sequent{ <H> >- 'n in label} -->
   sequent{ <H> >- field{'r;next{'n}} ~ (field{snd{'r};'n}) }

interactive_rw stepField_rw {| reduce |} :
   ('n in label) -->
   field{'r;next{'n}} <--> (field{snd{'r};'n})

(******************)
(*   Rules        *)
(******************)

(*** Typing ***)

interactive emptyRecordType {| intro [] |} :
   sequent{ <H> >- "type"{record} }

interactive recordType {| intro [] |} :
   sequent{ <H> >- "type"{'A} } -->
   sequent{ <H> >- 'n in label} -->
   sequent{ <H> >- "type"{record{'n;'A}} }

interactive record_elim1 'n :
   [wf] sequent{ <H> >- 'n in label } -->
   sequent{ <H> >- record{'n;'A} } -->
   sequent{ <H> >- "type"{'A} }

interactive recordTypeElimination{| elim [ThinOption thinT]  |} 'H :
   sequent{ <H>; u:"type"{record{'n;'A}}; <J['u]> >- 'n in label} -->
   sequent{ <H>; u:"type"{record{'n;'A}}; v:"type"{'A}; <J['u]> >- 'C['u] } -->
   sequent{ <H>; u:"type"{record{'n;'A}}; <J['u]> >- 'C['u] }


(*** Introductions ***)

interactive emptyRecordIntro {| intro[] |} :
   sequent{ <H> >-'r_1 = 'r_2 in record }

interactive recordEqualS5 :
   [wf] sequent{ <H> >- 'm in label } -->
   sequent{ <H> >- 'a1 ='a2 in 'A } -->
   sequent{ <H> >- rcrd{'m;'a1;'r1}=rcrd{'m;'a2;'r2} in record{'m;'A} }

interactive recordEqualS1 :
   [wf] sequent{ <H> >- 'n in label } -->
   [wf] sequent{ <H> >- 'm in label } -->
   [equality] sequent{ <H> >- not{.'n='m in label} } -->
   sequent{ <H> >- 'r1='r2 in record{'m;'A} } -->
   sequent{ <H> >- rcrd{'n;'a;'r1}='r2 in record{'m;'A} }

interactive recordEqualS4 :
   [wf] sequent{ <H> >- 'n in label } -->
   [wf] sequent{ <H> >- 'm in label } -->
   [equality] sequent{ <H> >- not{.'n='m in label} } -->
   sequent{ <H> >- 'r1=rcrd{'m;'a2;'r2} in record{'m;'A} } -->
   sequent{ <H> >- rcrd{'n;'a1;'r1}=rcrd{'m;'a2;'r2} in record{'m;'A} }

interactive recordEqualS2 :
   [wf] sequent{ <H> >- 'n in label } -->
   [wf] sequent{ <H> >- 'm in label } -->
   [equality] sequent{ <H> >- not{.'n='m in label} } -->
   sequent{ <H> >- 'r1='r2 in record{'m;'A} } -->
   sequent{ <H> >- 'r1=rcrd{'n;'a;'r2} in record{'m;'A} }

let record_eqcdST =
   firstT [recordEqualS5; recordEqualS4; recordEqualS2; recordEqualS1]

let resource intro += (<<'r1 = 'r2 in record{'m;'A} >>, wrap_intro record_eqcdST)

(*** Reductions ***)

interactive record_beta1 {| intro[] |} :
   [wf] sequent{ <H> >- 'n in label } -->
   sequent{ <H> >- field{rcrd{'n; 'a; 'r};'n} ~ 'a }

interactive record_beta2 {| intro[] |} :
   [wf] sequent{ <H> >- 'n in label } -->
   [wf] sequent{ <H> >- 'm in label } -->
   [equality] sequent{ <H> >- not{.'n ='m in label} } -->
   sequent{ <H> >- field{rcrd{'n; 'a; 'r};'m} ~ field{'r;'m} }

interactive record_eta  {| intro[] |}'A:
   [wf] sequent{ <H> >- 'n in label } -->
   [wf] sequent{ <H> >- 'r in record{'n;'A} } -->
   sequent{ <H> >- rcrd{'n; field{'r;'n}; 'r} ~ 'r }

interactive_rw record_eta_rw  :
   ('n in label ) -->
   ('r in record{'n;top} ) -->
   rcrd{'n; field{'r;'n}; 'r} <--> 'r


interactive record_cover  {| intro[] |} :
   [wf] sequent{ <H> >- 'n in label } -->
   sequent{ <H> >- rcrd{'n; 'a; rcrd{'n; 'b; 'r}} ~  rcrd{'n; 'a; 'r} }

interactive record_exchange {| intro[] |} :
   [wf] sequent{ <H> >- 'n in label } -->
   [wf] sequent{ <H> >- 'm in label } -->
   [equality] sequent{ <H> >- not{.'n='m in label} } -->
   sequent{ <H> >- rcrd{'n; 'a; rcrd{'m; 'b; 'r}} ~  rcrd{'m; 'b; rcrd{'n; 'a; 'r}} }


(*** Eliminations ***)

interactive field_member {| intro[] |} :
   [wf] sequent{ <H> >- 'n in label } -->
   sequent{ <H> >- 'r in record{'n;'A} } -->
   sequent{ <H> >- field{'r;'n} in 'A }




(******************)
(*  Display Forms *)
(******************)

doc <:doc< @docoff >>



dform emptyRecord_df : except_mode [src] :: record = `"{}"

dform emptyRcrd_df : except_mode [src] :: rcrd = `"{}"



dform field_df : except_mode [src] :: field{'r;'n} =  slot{'r} `"." slot{'n}



dform rcrd_df : except_mode [src] :: rcrd{'n;'a; 'r} = `"{" slot{'n} `"=" slot{'a} `";" slot{'r} `"}"


dform recordS_df : except_mode [src] :: record{'n;'A} = `"{" slot{'n} `":" slot{'A} `"}"












(*
let doubleInductionT =
 letT <<'rr='r in record>> thenAT autoT thenT thinT (-1) thenT moveToConclT 2
 thenT genAssumT [1;2;3] thenLT
    [repeatMForT 2 (dT 0 thenMT dT (-1) thenMT rwh reduceC 0) thenT autoT;
     assumT 3 thenT dT (-1) thenT autoT
    ]
*)

