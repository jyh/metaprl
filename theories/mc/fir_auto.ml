(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define automation tactics.
 *)

include Base_theory

open Top_conversionals

let firEvalT = rwh (repeatC (lowerC reduceTopC))
