extends Base_theory

open  Support_algebra
open Tactic_type.Conversionals
open Tactic_type.Tacticals



define unselectC: select{'A} <--> 'A

dform select_df:  select{'A} = `"[" 'A `"]"

interactive_rw  selectC:  'A <--> select{'A}

interactive_rw  ifSelectedC:  select{'A} <--> select{'A}
    (* does noting if term is selected, fails otherwise *)


let unselectT = rwhAllAll unselectC

let selectT assump clause = rwc selectC assump clause
let selectGoalT = rw selectC 0
let selectHypT n = rw selectC n
let selectAssumT n = selectT n 0


let rws conv = rwhAllAll (unselectC thenC conv)
  (*BUG: if conv fails or there is no selcted term then rws should also fail *)

let selectUpT = rwhAllAll (someSubC unselectC thenC selectC)
let selectDownT addr = rws (addrC addr selectC)

let selectSubAT first length =  rws (subAssocC  first length selectC)

let selectDownAT addr = rws (addrAssocC addr selectC)

let selectGoalDownT addr = selectGoalT thenT selectDownT addr

let selectGoalDownAT addr = selectGoalT thenT selectDownAT addr


