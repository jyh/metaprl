(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Operational semantics / judgements for FIR programs.
 *)

include Base_theory

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Evaluation judgement.
 * Declares that 'expr1 evaluates to 'expr2, i.e. the two
 *    computationally equivalent.
 *)
declare evals_to{ 'expr1; 'expr2 }

(*
 * Evaluation term.
 * Represents the evaluation of 'expr in the program state 'state.
 *)
declare eval{ 'state; 'expr }

(*
 * Value judgement.
 * Declares that 'atom does not access 'state, i.e. 'atom does
 *    not depend on 'state.
 *)
declare value{ 'state; 'atom }

(*
 * Non-value.
 * Term to represent a void / meaningless value.
 *)
declare dot
