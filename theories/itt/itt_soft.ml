(*
 * Regular logic connectives.
 *
 *)

include Tacticals
include Conversionals
include Base_dtactic
include Itt_equal

open Printf
open Debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermAddr
open Refine
open Resource

open Sequent
open Tacticals
open Conversionals
open Base_dtactic
open Itt_equal

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
let d_soft conv i =
   Conversionals.rw conv i thenT dT i

(*
 * Typehood.
 *)
let d_type_soft conv i =
   Conversionals.rw (addrC [0] conv) i thenT dT i

(*
 * EqCD.
 *)
let eqcd_soft conv =
   Conversionals.rw conv 0 thenT eqcdT

(*
 * Combine them.
 *)
let add_soft_abs dres eqcdres t rw =
   let type_t = mk_type_term t in
   let dres = dres.resource_improve dres (t, d_soft rw) in
   let dres = dres.resource_improve dres (type_t, d_type_soft rw) in
   let eqcdres = eqcdres.resource_improve eqcdres (t, eqcd_soft rw) in
      dres, eqcdres

(*
 * $Log$
 * Revision 1.7  1998/07/02 18:37:51  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.6  1998/06/03 22:19:45  jyh
 * Nonpolymorphic refiner.
 *
 * Revision 1.5  1998/06/01 13:56:16  jyh
 * Proving twice one is two.
 *
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
