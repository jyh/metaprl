extends Itt_dfun

open Refiner.Refiner.Term
open Tactic_type.Conversionals

rewrite reduceEta (x: 'A -> 'B['x]) : ('f in (x: 'A -> 'B['x])) -->
    lambda{x. 'f 'x} <--> 'f

topval reduceEtaC  : term -> conv
