extends Itt_record_label
extends Itt_record0
extends Itt_struct3
extends Itt_logic
extends Itt_disect

open Refiner.Refiner.Term
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals

val dest_field : term -> term * string
val mk_field_term : term -> string -> term

topval record_exchangeC : int -> conv

topval record_reduce : conv
topval record_reduceT : tactic
topval record_beta2 : conv
topval record_beta2_rw : conv

(*
topval record_eqcd : tactic
topval record_repeat_eqcd : tactic
*)
topval recordOrtT : tactic


define unfoldRcrd : rcrd[t:t]{'a;'r} <--> rcrd{label[t:t];'a;'r}

define unfoldRcrdS : rcrd[t:t]{'a} <--> rcrd[t:t]{'a;rcrd}

define unfoldField : field[t:t]{'r} <--> field{'r;label[t:t]}

define unfoldRecordS : record[t:t]{'A} <--> record{label[t:t];'A}

define unfoldRecordL : record[n:t]{self.'A['self];'R} <--> bisect{'R; self.record[n:t]{'A['self]}}

define unfoldRecordR : record[n:t]{'A;a.'R['a]} <--> bisect{record[n:t]{'A};r.'R[field[n:t]{'r}]}

define unfoldRecordI : record[n:t]{'A;'R} <--> record[n:t]{'A;a.'R}


declare self{'self}

declare self[n:t]{'x}
