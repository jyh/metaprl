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

(* Exponentiation assuming a non-negative, integral exponent. *)
define unfold_pow : pow{ 'base; 'exp } <-->
   ind{ 'exp; i, j. 1; 1; i, j. "mul"{'base; 'j} }
