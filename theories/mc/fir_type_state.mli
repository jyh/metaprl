(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Type judgements for FIR state operations.
 *)

include Base_theory
include Itt_theory
include Fir_state
include Fir_type

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Block type. *)
declare ty_block

(* Triple type. *)
declare ty_triple{ 'A; 'B; 'C }

(* State type. *)
declare ty_state

(* Reference type. *)
declare ty_ref
