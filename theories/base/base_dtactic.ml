(*
 * The D tactic performs a case selection on the conclusion opname.
 *)

open Printf
open Debug

open Opname
open Refiner.Refiner.Term
open Refiner.Refiner.TermAddr
open Refiner.Refiner.RefineErrors
open Resource
open Simple_print
open Term_table

open Tactic_type
open Sequent

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Base_dtactic%t" eflush

let debug_dtactic =
   create_debug (**)
      { debug_name = "dtactic";
        debug_description = "display dT tactic operations";
        debug_value = false
      }

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * The d_tactic uses a term_table to match against terms.
 *)
type d_data = (int -> tactic) term_table

resource (term * (int -> tactic), int -> tactic, d_data) d_resource

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Extract a D tactic from the data.
 * The tactic checks for an optable.
 *)
let extract_data tbl =
   let d i p =
      let t =
         (* Get the term described by the number *)
         if i = 0 then
            concl p
         else
            snd (nth_hyp p i)
      in
      let tac =
         try
            (* Find and apply the right tactic *)
            if !debug_dtactic then
               eprintf "Base_dtactic: lookup %s%t" (Simple_print.string_of_opname (opname_of_term t)) eflush;
            let _, _, tac = Term_table.lookup "Base_dtactic.extract_data" tbl t in
               tac
         with
            Not_found ->
               raise (RefineError ("extract_data", StringTermError ("D tactic doesn't know about", t)))
      in
         if !debug_dtactic then
            eprintf "Base_dtactic: applying %s%t" (Simple_print.string_of_opname (opname_of_term t)) eflush;
         tac i p
   in
      d

(*
 * Add a new tactic.
 *)
let improve_data (t, tac) tbl =
   Refine_exn.print Dform.null_base (insert tbl t) tac

(*
 * Wrap up the joiner.
 *)
let rec join_resource base1 base2 =
   let data = join_tables base1.resource_data base2.resource_data in
      { resource_data = data;
        resource_join = join_resource;
        resource_extract = extract_resource;
        resource_improve = improve_resource
      }

and extract_resource { resource_data = data } =
   extract_data data

and improve_resource { resource_data = data } x =
   if !debug_dtactic then
      begin
         let t, _ = x in
         let opname = opname_of_term t in
            eprintf "Base_dtactic.improve_resource: %s%t" (string_of_opname opname) eflush
      end;
   { resource_data = improve_data x data;
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

(*
 * Resource.
 *)
let d_resource =
   { resource_data = new_table ();
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

let dT = d_resource.resource_extract d_resource

(*
 * $Log$
 * Revision 1.9  1998/07/01 04:37:13  nogin
 * Moved Refiner exceptions into a separate module RefineErrors
 *
 * Revision 1.8  1998/06/15 22:32:38  jyh
 * Added CZF.
 *
 * Revision 1.7  1998/06/12 13:47:13  jyh
 * D tactic works, added itt_bool.
 *
 * Revision 1.6  1998/06/09 20:52:29  jyh
 * Propagated refinement changes.
 * New tacticals module.
 *
 * Revision 1.5  1998/06/01 13:55:38  jyh
 * Proving twice one is two.
 *
 * Revision 1.4  1998/05/28 13:47:13  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.3  1998/04/24 19:39:07  jyh
 * Updated debugging.
 *
 * Revision 1.2  1998/04/24 02:43:12  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.1  1997/04/28 15:51:55  jyh
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
 * Revision 1.2  1996/10/23 15:18:01  jyh
 * First working version of dT tactic.
 *
 * Revision 1.1  1996/09/25 22:52:09  jyh
 * Initial "tactical" commit.
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
