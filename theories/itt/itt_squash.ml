(*
 * We also define a resource to prove squash stability.
 * Terms are "squash stable" if their proof can be inferred from the
 * fact that they are true.  The general form is a squash
 * proof is just:
 *     sequent [it; squash] { H >> T } -->
 *     sequent [it; it] { H >> T }
 *)

include Tacticals
include Sequent
include Base_theory

open Printf
open Nl_debug
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Term_stable
open Resource

open Tacticals
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
let is_squash_sequent goal =
   let args = args_of_sequent goal in
      match dest_xlist args with
         [flag] ->
            opname_of_term flag == squash_opname
       | _ ->
            false

let get_squash_arg goal =
   let args = args_of_sequent goal in
      match dest_xlist args with
         [flag] ->
            flag
       | _ ->
            raise (RefineError ("get_squash_arg", StringError "no argument"))

let is_squash_goal p =
   is_squash_sequent (goal p)

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
               raise (RefineError ("squash", StringTermError ("SQUASH tactic doesn't know about ", t)))
   in
      squash

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
let rec join_resource { resource_data = data1 } { resource_data = data2 } =
   { resource_data = join_stables data1 data2;
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource;
     resource_close = close_resource
   }

and extract_resource { resource_data = data } =
   extract_data data

and improve_resource { resource_data = data } (t, tac) =
   { resource_data = sinsert data t tac;
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
let squash_resource =
   { resource_data = new_stable ();
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource;
     resource_close = close_resource
   }

(*
 * Resource argument.
 *)
let squashT p =
   Sequent.get_tactic_arg p "squash" p

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
