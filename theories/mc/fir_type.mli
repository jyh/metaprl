(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define a type system for FIR types.
 *)

include Base_theory
include Itt_theory
include Fir_ty

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Universe of FIR types. *)
declare fir_univ

(*
 * Disjoint union type.
 * Necessary since inl/inr equality in ITT_union
 * depends on the ITT_equal!"type" jugdement.
 *)
declare dunion{ 'A; 'B }
declare inl{'x}
declare inr{'x}

(*
 * Array type.  Essentially lists.
 * Necessary since the nil/cons membership rules for the ITT list
 * type depend on the Itt_equal!"type" judgement, which may
 * not hold for FIR types.
 *)
declare array{ 'A }

(*
 * Function type from 'A to 'B.
 * Necessary since ITT "fun"s are required to terminate, where as
 * FIR functions may not.
 *)
declare ty_fun{ 'A; 'B }

(*
 * Recursive type.
 * Itt_srec is not sufficient since that won't allow something like:
 *    type 'a term = Int of int | Fun of ('a term -> 'a term)
 *)
declare "rec"{ X. 'A['X] }

(* Integer set type. *)
declare ty_interval
declare ty_int_set

(*
 * FIR value type.
 * Used to abstract the type of an FIR value.
 *)
declare fir_value
