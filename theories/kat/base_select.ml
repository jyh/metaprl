extends Base_theory

open Tactic_type.Conversionals

define unselectC: select{'A} <--> 'A

interactive_rw  selectC:  'A <--> select{'A}

interactive_rw  ifSelectedC:  select{'A} <--> select{'A}
    (* does noting if term is selected, fails otherwise *)


let onSelectedC conv = higherC (unselectC thenC conv)
let rws conv = rwhAll (unselectC thenC conv)

let selectUpC = (someSubC unselectC) thenC selectC
let selectDownC addr = onSelectedC (addrC addr selectC)

dform select_df:  select{'A} = `"[" 'A `"]"

