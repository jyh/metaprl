include Itt_record_label
include Itt_record0
include Itt_struct3

open Refiner.Refiner.Term
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals


topval record_exchangeC : int -> conv




define unfoldRecordS : record[t:s]{'A} <--> record{label[t:s];'A}

define unfoldRecord : record[t:s]{'A;'R} <--> record{label[t:s];'A;'R}

define unfoldRcrd : rcrd[t:s]{'a;'r} <--> rcrd{label[t:s];'a;'r}

define unfoldRcrdS : rcrd[t:s]{'a} <--> rcrd[t:s]{'a;rcrd}

define unfoldField : field[t:s]{'r} <--> field{'r;label[t:s]}

define unfoldRecordOrt : record_ort[t:s]{'a;'R} <--> record_ort{label[t:s];'a;'R}

topval unfoldAllT : tactic
