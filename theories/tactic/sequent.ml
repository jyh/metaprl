(*
 * Utilities for tactics.
 *)

open Printf
open Debug

open Refiner.Refiner

(*
 * Debug statement.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Sequent%t" eflush

(*
 * Construction.
 *)
let create = Tactic_type.create

(*
 * Addressing.
 *)
let goal = Tactic_type.goal

let concl arg =
   Tactic_type.nth_concl arg 0

let nth_hyp = Tactic_type.nth_hyp

let cache = Tactic_type.cache

let label = Tactic_type.label

let resources = Tactic_type.resources

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
         i, count - i

let clause_addr arg i =
   TermMan.nth_clause_addr (goal arg) i

let get_decl_number arg v =
   TermMan.get_decl_number (goal arg) v

let declared_vars arg =
   TermMan.declared_vars (goal arg)

let explode_sequent arg =
   TermMan.explode_sequent (goal arg)

let is_free_seq_var i v arg =
   TermMan.is_free_seq_var i v (goal arg)

(*
 * $Log$
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
