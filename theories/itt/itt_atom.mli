(*
 * Atom is the type of tokens (strings)
 *
 *)

open Term

(*
 * Derived from baseTheory.
 *)
include Itt_equal

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare atom
declare token[@t:t]

val atom_term : term
val bogus_token : term

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
 * H >- Atom ext "t"
 * by tokenFormation "t"
 *)
axiom tokenFormation 'H token[@t:t] : sequent ['ext] { 'H >- atom }

(*
 * H >- "t" = "t" in Atom
 * by tokenEquality
 *)
axiom tokenEquality 'H : sequent ['ext] { 'H >- token[@t:t] = token[@t:t] in atom }

(*
 * $Log$
 * Revision 1.1  1997/04/28 15:52:07  jyh
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
 * Revision 1.7  1996/09/25 22:52:11  jyh
 * Initial "tactical" commit.
 *
 * Revision 1.6  1996/09/02 19:37:17  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.5  1996/05/21 02:16:34  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.4  1996/04/11 13:33:50  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.3  1996/03/28 02:51:27  jyh
 * This is an initial version of the type theory.
 *
 * Revision 1.2  1996/03/05 19:59:40  jyh
 * Version just before LogicalFramework.
 *
 * Revision 1.1  1996/02/13 21:35:56  jyh
 * Intermediate checkin while matching is bing added to the refiner.
 *
 * -*-
 * Local Variables:
 * Caml-master: "manager"
 * End:
 * -*-
 *)
