(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define and implement operations for ints in the FIR.
 *)

include Base_theory
include Itt_theory
include Fir_ty
include Fir_exp

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Unary and bitwise negation. *)
declare uminusIntOp
declare notIntOp

(* Standard binary arithmetic operators. *)
declare plusIntOp
declare minusIntOp
declare mulIntOp
declare divIntOp
declare remIntOp

(*
 * Binary bitwise operators:
 * and, or, xor
 * logical shifts left/right
 * arithmetic shift right
 *
 * The implementation of these will be completed once ints in the FIR
 * are properly formalized.  Until then, only lsl, lsr, and asr will
 * be implemented, and these three will all do arithmetic shifts.
 *)
declare lslIntOp
declare lsrIntOp
declare asrIntOp
declare andIntOp
declare orIntOp
declare xorIntOp

(* Max / min. *)
declare maxIntOp
declare minIntOp

(* Boolean comparisons. *)
declare eqIntOp
declare neqIntOp
declare ltIntOp
declare leIntOp
declare gtIntOp
declare geIntOp
declare cmpIntOp

(*************************************************************************
 * Rewrites.
 *************************************************************************)

topval reduce_uminusIntOp : conv
topval reduce_plusIntOp : conv
topval reduce_minusIntOp : conv
topval reduce_mulIntOp : conv
topval reduce_divIntOp : conv
topval reduce_remIntOp : conv
topval reduce_maxIntOp : conv
topval reduce_minIntOp : conv
topval reduce_eqIntOp : conv
topval reduce_neqIntOp : conv
topval reduce_ltIntOp : conv
topval reduce_leIntOp : conv
topval reduce_gtIntOp : conv
topval reduce_geIntOp : conv
topval reduce_cmpIntOp : conv
