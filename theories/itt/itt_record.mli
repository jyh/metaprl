include Itt_record_label
include Itt_record0
include Itt_struct3
include Itt_logic
include Itt_disect

open Refiner.Refiner.Term
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals


topval record_exchangeC : int -> conv

topval record_reduce : conv
topval record_reduceT : tactic
topval record_beta2 : conv
topval record_beta2_rw : conv

topval record_eqcd : tactic
topval record_repeat_eqcd : tactic


define unfoldRcrd : rcrd[t:t]{'a;'r} <--> rcrd{label[t:t];'a;'r}

define unfoldRcrdS : rcrd[t:t]{'a} <--> rcrd[t:t]{'a;rcrd}

define unfoldField : field[t:t]{'r} <--> field{'r;label[t:t]}

define unfoldRecordS : record[t:t]{'A} <--> record{label[t:t];'A}

define unfoldRecordL : record[n:t]{self.'A['self];'R} <--> disect{'R; self.record[n:t]{'A['self]}}

define unfoldRecordR : record[n:t]{'A;a.'R['a]} <--> disect{record[n:t]{'A};r.'R[field[n:t]{'r}]}

define unfoldRecordI : record[n:t]{'A;'R} <--> record[n:t]{'A;a.'R}

