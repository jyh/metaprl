(*
 * Utilities for tactics.
 *)

open Printf
open Debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine

open Tactic_type

(*
 * Debug statement.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Sequent%t" eflush

(*
 * Construction.
 *)
let create = create_arg

let dest = dest_arg

let arg = tactic_arg

let goal p =
   (tactic_seq p).mseq_goal

let concl p =
   nth_concl (goal p) 0

let concl_addr p =
   nth_concl_addr (goal p) 0

let hyp_addr p i =
   let goal = goal p in
      if i < 0 then
         nth_address ((num_hyps goal) + i) true
      else
         nth_hyp_addr goal i

let clause_addr p i =
   if i = 0 then
      concl_addr p
   else
      hyp_addr p i

let var_of_hyp i p =
   fst (TermMan.nth_hyp (goal p) i)

let hyp_count p =
   num_hyps (goal p)

let get_decl_number p v =
   TermMan.get_decl_number (goal p) v

let nth_hyp i p =
   let _, h = TermMan.nth_hyp (goal p) i in
      h

let declared_vars p =
   TermMan.declared_vars (goal p)

let get_pos_hyp_index i count =
   if i < 0 then
      count - i
   else
      i

let get_pos_hyp_num i p =
   if i < 0 then
      (num_hyps (goal p)) - i
   else
      i

(*
 * $Log$
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
