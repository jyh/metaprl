(*
 * Before anything, we start the type inference resource.
 * This is mostly an incomplete type inference algorithm, but
 * it is used to perform basic inference.
 *)

include Tacticals

open Printf
open Debug

open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Term_table
open Resource

open Tacticals
open Sequent

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Typeinf%t" eflush

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * This is the type of the inference algorithm.
 *)
type typeinf_func = term_subst -> term -> term_subst * term

(*
 * Modular components also get a recursive instance of
 * the inference algorithm.
 *)
type typeinf_comp = typeinf_func -> typeinf_func

(*
 * This is the resource addition.
 *)
type typeinf_resource_info = term * typeinf_comp

(*
 * Internal type.
 *)
type typeinf_data = typeinf_comp term_table

(*
 * The resource itself.
 *)
resource (typeinf_resource_info, typeinf_func, typeinf_data) typeinf_resource

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Infer the type of a term from the table.
 *)
let infer tbl =
   let rec aux decl t =
      let _, _, inf =
         try lookup "Typeinf.infer" tbl t with
            Not_found ->
               raise (RefineError ("typeinf", StringTermError ("can't infer type for", t)))
      in
         inf aux decl t
   in
      aux

(*
 * Wrap up the algorithm.
 *)
let rec join_resource { resource_data = tbl1 } { resource_data = tbl2 } =
   let data = join_tables tbl1 tbl2 in
      { resource_data = data;
        resource_join = join_resource;
        resource_extract = extract_resource;
        resource_improve = improve_resource
      }

and extract_resource { resource_data = tbl } =
   infer tbl

and improve_resource { resource_data = tbl } (t, inf) =
   { resource_data = insert tbl t inf;
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

(*
 * Resource.
 *)
let typeinf_resource =
   { resource_data = new_table ();
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

(*
 * Projector.
 *)
let typeinf_of_proof p =
   get_typeinf_arg p "typeinf"

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
