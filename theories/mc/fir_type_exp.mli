(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define a type system for FIR expressions.
 *)

include Base_theory
include Itt_theory
include Fir_int_set
include Fir_exp
include Fir_type
include Fir_type_state

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Judgement that a match statement produces a match. *)
declare produces_match{ 'key; 'cases }

(* Allocation operator type. *)
declare ty_alloc_op

(*************************************************************************
 * Rewrites.
 *************************************************************************)

topval reduce_produces_match_base : conv
topval reduce_produces_match_ind : conv
