(*
 * Utilities for tactics.
 *)

open Printf
open Debug

open Refiner.Refiner
open Refiner.Refiner.Refine

(*
 * Debug statement.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Sequent%t" eflush

(*
 * Types.
 *)
type extract = Tactic_type.extract
type tactic_arg = Tactic_type.tactic_arg
type tactic_value = Tactic_type.tactic_value
type cache = Tactic_type.cache
type attributes = Tactic_type.attributes

(*
 * Construction.
 *)
let create = Tactic_type.create

(*
 * Two tactic_arguments are equal when they have
 * equal msequent parts.  Their labels, etc, are
 * not compared.
 *)
let tactic_arg_alpha_equal = Tactic_type.tactic_arg_alpha_equal

(*
 * Addressing.
 *)
let goal = Tactic_type.goal

let msequent = Tactic_type.msequent

let concl arg =
   Tactic_type.nth_concl arg 0

let nth_hyp = Tactic_type.nth_hyp

let cache = Tactic_type.cache

let label = Tactic_type.label

let attributes = Tactic_type.attributes

(*
 * Sequent parts.
 *)
let hyp_count arg =
   TermMan.num_hyps (goal arg)

let hyp_indices arg i =
   let count = hyp_count arg in
      if i < 0 then
         count + i, count + i - 1
      else
         i - 1, count - i

let clause_addr arg i =
   TermMan.nth_clause_addr (goal arg) i

let get_decl_number arg v =
   TermMan.get_decl_number (goal arg) v

let declared_vars arg =
   let seq = msequent arg in
   let vars, goal, _ = dest_msequent_vars seq in
      vars @ (TermMan.declared_vars goal)

let explode_sequent arg =
   TermMan.explode_sequent (goal arg)

let is_free_seq_var i v arg =
   TermMan.is_free_seq_var i v (goal arg)

(*
 * Modification of the argument.
 * These are functional.
 *)
let set_goal  = Tactic_type.set_goal
let set_concl = Tactic_type.set_concl
let set_label = Tactic_type.set_label

(*
 * Argument functions.
 *)
let get_term_arg       = Tactic_type.get_term
let get_type_arg       = Tactic_type.get_type
let get_int_arg        = Tactic_type.get_int
let get_bool_arg       = Tactic_type.get_bool
let get_subst_arg      = Tactic_type.get_subst
let get_tactic_arg     = Tactic_type.get_tactic
let get_int_tactic_arg = Tactic_type.get_int_tactic
let get_typeinf_arg    = Tactic_type.get_typeinf

(*
 * $Log$
 * Revision 1.9  1998/07/02 22:25:30  jyh
 * Created term_copy module to copy and normalize terms.
 *
 * Revision 1.8  1998/06/16 16:26:21  jyh
 * Added itt_test.
 *
 * Revision 1.7  1998/06/15 22:33:45  jyh
 * Added CZF.
 *
 * Revision 1.6  1998/06/09 20:52:54  jyh
 * Propagated refinement changes.
 * New tacticals module.
 *
 * Revision 1.5  1998/06/03 22:19:58  jyh
 * Nonpolymorphic refiner.
 *
 * Revision 1.4  1998/05/28 13:48:33  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.3  1998/04/24 02:44:01  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.2  1998/04/21 19:55:16  jyh
 * Upgraded refiner for program extraction.
 *
 * Revision 1.1  1997/04/28 15:52:41  jyh
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
 * Revision 1.1  1996/09/25 22:52:06  jyh
 * Initial "tactical" commit.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
