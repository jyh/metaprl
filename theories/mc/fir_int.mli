(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define and implement operations for ML ints.
 *)

include Itt_theory
include Fir_exp

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *
 * These are operations on integers (2's complement internal
 * representation is assumed) -
 *    Unary operators:
 *       uminus - unary negation
 *       not - bit inversion
 *    Binary operators:
 *       plus, minus, mul, div, rem - standard arithmetic operations
 *       lsl, lsr - logical shift left / right (don't preserve sign)
 *       asr - arithmetic shift right (preserve sign)
 *       and, or, xor - standard bitwise operators
 *       eq, lt, le, gt, ge - comparison ( =, <, <=, >, >= )
 *       pow - exponentiation, assuming a non-negative exponent.
 *
 * NOTE: lsl, lsr, and asr all do arithmetic shifts right now.
 *       They also assume that the shift ammount is non-negative.
 *       They also dont' take into account the storage space
 *       available for that int. These should be fixed eventually.
 *       Also, div and rem don't seem to reduce properly, as of yet.
 *************************************************************************)

declare uminusIntOp
declare notIntOp

declare plusIntOp
declare minusIntOp
declare mulIntOp
declare divIntOp
declare remIntOp

declare lslIntOp
declare lsrIntOp
declare asrIntOp
declare andIntOp
declare orIntOp
declare xorIntOp

declare eqIntOp
declare ltIntOp
declare leIntOp
declare gtIntOp
declare geIntOp

declare pow{ 'base; 'exp }
topval unfold_pow : conv
