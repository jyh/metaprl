(*
 * Atom is the type of tokens (strings)
 *
 *)

(*
 * Derived from baseTheory.
 *)
include Itt_equal

open Refiner.Refiner.Term

open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare atom
declare token[@t:t]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Atom
 * by atomFormation
 *)
axiom atomFormation 'H : sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- Atom = Atom in Ui ext Ax
 * by atomEquality
 *)
axiom atomEquality 'H : sequent ['ext] { 'H >- atom = atom in univ[@i:l] }

(*
 * Typehood.
 *)
axiom atomType 'H : sequent ['ext] { 'H >- "type"{atom} }

(*
 * H >- Atom ext "t"
 * by tokenFormation "t"
 *)
axiom tokenFormation 'H token[@t:t] : sequent ['ext] { 'H >- atom }

(*
 * H >- "t" = "t" in Atom
 * by tokenEquality
 *)
axiom tokenEquality 'H : sequent ['ext] { 'H >- token[@t:t] = token[@t:t] in atom }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_atomT : int -> tactic
val eqcd_atomT : tactic
val eqcd_tokenT : tactic

val atom_term : term

val token_term : term
val bogus_token : term
val is_token_term : term -> bool
val dest_token : term -> string
val mk_token_term : string -> term

(*
 * -*-
 * Local Variables:
 * Caml-master: "manager"
 * End:
 * -*-
 *)
