(*
 * The D tactic performs a case selection on the conclusion opname.
 *)

include Base_auto_tactic

open Printf
open Nl_debug

open Opname
open Refiner.Refiner.Term
open Refiner.Refiner.TermAddr
open Refiner.Refiner.RefineError
open Resource
open Simple_print
open Term_table

open Tacticals
open Sequent

open Base_auto_tactic
open Nltop

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
 * Keep a list of resources for lookup by the toploop.
 *)
let resources = ref []

let save name rsrc =
   resources := (name, rsrc) :: !resources

let get_resource name =
   let rec search = function
      (name', rsrc) :: tl ->
         if name' = name then
            rsrc
         else
            search tl
    | [] ->
         raise Not_found
   in
      search !resources

(*
 * Wrap up the joiner.
 *)
let rec join_resource base1 base2 =
   let data = join_tables base1.resource_data base2.resource_data in
      { resource_data = data;
        resource_join = join_resource;
        resource_extract = extract_resource;
        resource_improve = improve_resource;
        resource_close = close_resource
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
     resource_improve = improve_resource;
     resource_close = close_resource
   }

and close_resource rsrc modname =
   save modname rsrc;
   rsrc

(*
 * Resource.
 *)
let d_resource =
   { resource_data = new_table ();
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource;
     resource_close = close_resource
   }

let dT i p =
   Sequent.get_int_tactic_arg p "d" i p

let rec dForT i =
   if i <= 0 then
      idT
   else
      dT 0 thenMT dForT (i - 1)

(*
 * By default, dT 0 should always make progress.
 *)
let d_prec = create_auto_prec [trivial_prec] []

let auto_resource =
   auto_resource.resource_improve auto_resource (**)
      { auto_name = "dT";
        auto_prec = d_prec;
        auto_tac = auto_wrap (dT 0)
      }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
