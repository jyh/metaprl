(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define and implement the basic expression forms in the FIR.
 *
 * Todo:
 *    -  Make sure all the necessary declarations are here and doc'ed
 *       appropriately.
 *)

include Base_theory
include Itt_theory
include Fir_ty
include Fir_int_set

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Inlined operators.
 *)

(* Identity (polymorphic). *)
declare idOp

(*
 * Allocation operators.
 * copy makes a list with 'len copies of 'init.
 * 'len should be a positive number.
 *)

declare allocSafe{ 'tag; 'args }
declare allocArray{ 'len; 'init }
define unfold_copy : copy{ 'len; 'init } <-->
   ind{'len; i, j. nil; nil; i, j. cons{'init; 'j}}

(*
 * Expressions.
 *)

(* Function application. *)
declare unOp{ 'op; 'a1; v. 'exp['v] }
declare binOp{ 'op; 'a1; 'a2; v. 'exp['v] }
(*declare tailCall*)

(* Control. *)
declare matchCase{ 'set; 'exp }
declare "match"{ 'a; 'cases }

(* Allocation. *)
declare letAlloc{ 'op; v. 'exp['v] }

(* Subscripting. *)
declare letSubscript{ 'block; 'index; v. 'exp['v] }
(*declare setSubscript{ 'a1; 'a2; 'a3; 'exp }*)
declare letSubCheck{ 'a1; 'a2; 'a3; 'exp }
