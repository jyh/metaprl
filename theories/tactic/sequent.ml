(*
 * Utilities for tactics.
 *)

open Printf
open Debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine

(*
 * Debug statement.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Sequent%t" eflush

(*
 * Sequent operations.
 *)
let get_pos_hyp_index i count =
   if i < 0 then
      count - i
   else
      i

let get_pos_hyp_num i { tac_goal = t } =
   if i < 0 then
      (num_hyps t) - i
   else
      i

let var_of_hyp i { tac_goal = t } =
   fst (TermMan.nth_hyp t i)

let hyp_count { tac_goal = t } =
   num_hyps t

let get_decl_number { tac_goal = t } v =
   TermMan.get_decl_number t v

let nth_hyp i { tac_goal = t } =
   let _, h = TermMan.nth_hyp t i in
      h

let declared_vars { tac_goal = t } =
   TermMan.declared_vars t

let concl { tac_goal = t } = nth_concl t 0

let goal { tac_goal = t } = t

(*
 * $Log$
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
