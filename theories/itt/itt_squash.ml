(*
 * We also define a resource to prove squash stability.
 * Terms are "squash stable" if their proof can be inferred from the
 * fact that they are true.  The general form is a squash
 * proof is just:
 *     sequent [it; squash] { H >> T } -->
 *     sequent [it; it] { H >> T }
 *)

include Tactic_type
include Sequent

open Printf
open Debug
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine
open Term_stable
open Resource

open Tactic_type
open Sequent

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_squash%t" eflush

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare ext
declare squash

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * Keep a table of tactics to prove squash stability.
 *)
type squash_data = tactic term_stable

(*
 * The resource itself.
 *)
resource (term * tactic, tactic, squash_data) squash_resource

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let squash_term = << squash >>
let squash_opname = opname_of_term squash_term

(*
 * Is a goal squashed?
 *)
let is_squash_goal p =
   match dest_sequent (goal p) with
      [_; _; flag] ->
         opname_of_term flag == squash_opname
    | _ ->
         false

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Extract an SQUASH tactic from the data.
 * The tactic checks for an optable.
 *)
let extract_data base =
   let tbl = sextract base in
   let squash p =
      let t = concl p in
         try (slookup tbl t) p with
            Not_found ->
               raise (RefineError (StringTermError ("SQUASH tactic doesn't know about ", t)))
   in
      squash

(*
 * Wrap up the joiner.
 *)
let rec join_resource { resource_data = data1 } { resource_data = data2 } =
   { resource_data = join_stables data1 data2;
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

and extract_resource { resource_data = data } =
   extract_data data

and improve_resource { resource_data = data } (t, tac) =
   { resource_data = sinsert data t tac;
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

(*
 * Resource.
 *)
let squash_resource =
   { resource_data = new_stable ();
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

(*
 * Resource argument.
 *)
let squash_of_proof p =
   let { ref_squash = squash } = Sequent.resources p in
      squash

(*
 * $Log$
 * Revision 1.8  1998/06/09 20:52:45  jyh
 * Propagated refinement changes.
 * New tacticals module.
 *
 * Revision 1.7  1998/06/03 22:19:47  jyh
 * Nonpolymorphic refiner.
 *
 * Revision 1.6  1998/06/01 13:56:19  jyh
 * Proving twice one is two.
 *
 * Revision 1.5  1998/05/28 13:48:06  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.4  1998/04/24 02:43:48  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.3  1998/04/22 22:45:13  jyh
 * *** empty log message ***
 *
 * Revision 1.2  1998/04/21 19:54:56  jyh
 * Upgraded refiner for program extraction.
 *
 * Revision 1.1  1997/08/06 16:18:42  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
