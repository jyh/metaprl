(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define and implement the basic expression forms for the FIR.
 *
 * Todo:
 *    - documentation as necessary, if not for others, then for me :)
 *    - make sure all the necessary declarations are here
 *)

include Base_theory
include Itt_theory

open Refiner.Refiner.Term
open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Memory is allocated in blocks.
 * Each block has a tag and some values (a list).
 *)

declare block{ 'tag; 'args }

(*
 * Inlined operators.
 *)

(* Identity (polymorphic). *)
declare idOp

(*
 * Allocation operators.
 * copy makes a list with 'len copies of 'init.
 *)

declare allocSafe{ 'tag; 'args }
declare allocArray{ 'len; 'init }
declare copy{ 'len; 'init }

(*
 * Normal values.
 *)

(*declare atomInt{ 'int }*)
(*declare atomVar{ 'var }*)

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

(*************************************************************************
 * Rewrites and term operations.
 *************************************************************************)

topval unfold_copy : conv

val matchCase_term : term
val is_matchCase_term : term -> bool
val mk_matchCase_term : term -> term -> term
val dest_matchCase : term -> term * term

val match_term : term
val is_match_term : term -> bool
val mk_match_term : term -> term -> term
val dest_match : term -> term * term
