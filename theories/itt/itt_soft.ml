(*
 * Regular logic connectives.
 *
 *)

include Tactic_type

include Itt_equal

open Printf
open Debug
open Refiner.Refiner.Term
open Refine
open Resource

open Sequent

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_soft%t" eflush

(* debug_string DebugLoad "Loading itt_soft..." *)

(*
 * D tactic.
 *)
let d_soft rw i p =
   let count = hyp_count p in
   let i' =
      if i = 0 then
         count
      else
         get_pos_hyp_index i count
   in
      (Refiner.rwtactic (Refiner.rwaddr (make_seq_address i') rw)) p
       
(*
 * EqCD.
 *)
let eqcd_soft rw p =
   (Refiner.rwtactic (Refiner.rwaddr (make_seq_address (hyp_count p)) rw)) p

(*
 * Combine them.
 *)
let add_soft_abs dres eqcdres t rw =
   dres.resource_improve dres (t, d_soft rw),
   eqcdres.resource_improve eqcdres (t, eqcd_soft rw)

(*
 * $Log$
 * Revision 1.4  1998/05/28 13:48:03  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.3  1998/04/24 02:43:46  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.2  1998/04/22 22:45:11  jyh
 * *** empty log message ***
 *
 * Revision 1.1  1997/04/28 15:52:26  jyh
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
 * Revision 1.1  1996/10/23 15:18:12  jyh
 * First working version of dT tactic.
 *
 * Revision 1.3  1996/09/25 22:52:13  jyh
 * Initial "tactical" commit.
 *
 * Revision 1.2  1996/09/02 19:37:30  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.1  1996/06/11 18:38:38  jyh
 * Demo version 0.0
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
