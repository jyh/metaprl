(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define a type system for FIR types.
 *)

include Base_theory
include Itt_theory
include Fir_ty

open Tactic_type.Conversionals

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
declare apply
declare lambda
*)

(*
 * Universally quantified type.
 * x varies over all types in fir_univ.
 *)
declare ty_all{ x. 'ty['x] }

(*
 * Existentially quantified type.
 * There is a type x in fir_univ such that...
 *)
declare ty_exists{ x. 'ty['x] }

(*
 * Recursive type.
 * Itt_srec is not sufficient since that won't allow something like:
 *    type 'a term = Int of int | Fun of ('a term -> 'a term)
 *)
declare "rec"{ x. 'ty['x] }

(* Integer set type. *)
declare ty_interval
declare ty_int_set

(*
 * FIR value type.
 * Used to abstract the type of an FIR value.
 *)
declare fir_value

(*************************************************************************
 * Rewrites.
 *************************************************************************)

topval reduce_tyInt : conv
topval reduce_tyFun1 : conv
topval reduce_tyFun2 : conv
topval reduce_tyTuple1 : conv
topval reduce_tyTuple2 : conv
topval reduce_tyArray : conv
topval reduce_tyExists1 : conv
topval reduce_tyExists2 : conv
topval reduce_tyAll1 : conv
topval reduce_tyAll2 : conv
