(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define automation tactics.
 *)

include Base_theory

open Tactic_type.Conversionals

topval firEvalT : int -> tactic
