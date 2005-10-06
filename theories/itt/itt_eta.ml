doc <:doc<
   @module[Itt_eta]
   @parents
>>
extends Itt_fun

open Basic_tactics

doc <:doc<

   The @tt[reduceEta] rewrite defines eta-reduction.
   This is conditional reduction: one can apply it only for functions.
>>

prim_rw reduceEta (x: 'A -> 'B['x]) :
   ('f in (x: 'A -> 'B['x])) -->
    lambda{x. 'f 'x} <--> 'f

let reduceEtaC = reduceEta

interactive elim_eta_undep 'H :
    sequent { <H>; f: 'A -> 'B; <J['f]> >- 'C[lambda{x. 'f 'x}] } -->
    sequent { <H>; f: 'A -> 'B; <J['f]> >- 'C['f] }

interactive elim_eta_dep 'H :
    sequent { <H>; f: x: 'A -> 'B['x]; <J['f]> >- 'C[lambda{x. 'f 'x}] } -->
    sequent { <H>; f: x: 'A -> 'B['x]; <J['f]> >- 'C['f] }

