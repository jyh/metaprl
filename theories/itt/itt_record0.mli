include Itt_record_label0
include Itt_struct3
include Itt_inv_typing

open Refiner.Refiner.Term
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals
open Itt_inv_typing


declare record{}
declare record{'n;'A}
declare record{'n;'A;'R}
declare rcrd{'n;'a;'r}
declare rcrd{'n;'a}
declare rcrd{}
declare field{'r;'n}

define unfoldRecordOrt : record_ort{'n;'a;'R} <--> (all r:'R. (rcrd{'n;'a;'r} IN 'R))

topval foldRecord : conv



