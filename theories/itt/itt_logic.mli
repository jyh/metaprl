(*
 * Standard logical connectives.
 *
 *)

open Term

include Itt_equal
include Itt_dprod
include Itt_union
include Itt_void
include Itt_unit
include Itt_soft

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

define reduceTrue : "true" <--> unit
define reduceFalse : "false" <--> void

define reduceNot : "not"{'a} <--> 'a -> void

define reduceImplies : "implies"{'a; 'b} <--> 'a -> 'b
define reduceAnd : "and"{'a; 'b} <--> 'a * 'b
define reduceOr : "or"{'a; 'b} <--> 'a + 'b

define reduceAll : "all"{'A; x. 'B['x]} <--> x: 'A -> 'B['x]
define reduceExists : "exists"{'A; x. 'B['x]} <--> x: 'A * 'B['x]

(************************************************************************
 * DISPLAY FORMS							*
 ************************************************************************)

prec prec_implies
prec prec_and
prec prec_or
prec prec_quant

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val is_true_term : term -> bool
val true_term : term

val is_false_term : term -> bool
val false_term : term

val is_all_term : term -> bool
val dest_all : term -> string * term * term
val mk_all_term : string -> term -> term -> term

val is_exists_term : term -> bool
val dest_exists : term -> string * term * term
val mk_exists_term : string -> term -> term -> term

val is_or_term : term -> bool
val dest_or : term -> term * term
val mk_or_term : term -> term -> term

val is_and_term : term -> bool
val dest_and : term -> term * term
val mk_and_term : term -> term -> term

val is_implies_term : term -> bool
val dest_implies : term -> term * term
val mk_implies_term : term -> term -> term

val is_not_term : term -> bool
val dest_not : term -> term
val mk_not_term : term -> term

(*
 * $Log$
 * Revision 1.2  1997/08/06 16:18:35  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:18  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 * Revision 1.4  1996/10/23 15:18:09  jyh
 * First working version of dT tactic.
 *
 * Revision 1.3  1996/09/25 22:52:13  jyh
 * Initial "tactical" commit.
 *
 * Revision 1.2  1996/09/02 19:37:31  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.1  1996/06/11 18:38:40  jyh
 * Demo version 0.0
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
