extends Itt_dfun

open Basic_tactics

rewrite reduceEta (x: 'A -> 'B['x]) : ('f in (x: 'A -> 'B['x])) -->
    lambda{x. 'f 'x} <--> 'f

topval reduceEtaC  : term -> conv
