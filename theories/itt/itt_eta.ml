(*!
 * @spelling{reduceEta}
 *
 * @begin[doc]
 * @theory[Itt_eta]
 * @parents
 * @end[doc]
 *)
extends Itt_dfun

(*!
 * @begin[doc]
 *
 * The @tt{reduceEta} rewrite defines eta-reduction.
 * This is conditional reduction: one can apply it only for functions.
 * @end[doc]
 *)

 prim_rw reduceEta (x: 'A -> 'B['x]) :
   ('f IN (x: 'A -> 'B['x])) -->
    lambda{x. 'f 'x} <--> 'f

let reduceEtaC = reduceEta
