(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define a type system for FIR expressions.
 *)

include Base_theory
include Itt_equal
include Fir_int_set
include Fir_exp
include Fir_type
include Fir_type_state

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Judgement that a match statement produces a match. *)
declare produces_match{ 'key; 'cases }
