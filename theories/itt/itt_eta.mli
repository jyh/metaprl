include Itt_dfun

rewrite reduceEta (x: 'A -> 'B['x]) : ('f IN (x: 'A -> 'B['x])) -->
    lambda{x. 'f 'x} <--> 'f
