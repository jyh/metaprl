(*
 * Before anything, we start the type inference resource.
 * This is mostly an incomplete type inference algorithm, but
 * it is used to perform basic inference.
 *
 * $Log$
 * Revision 1.7  1998/05/01 14:59:46  jyh
 * Updating display forms.
 *
 * Revision 1.6  1998/04/29 14:48:41  jyh
 * Added ocaml_sos.
 *
 * Revision 1.5  1998/04/24 19:39:13  jyh
 * Updated debugging.
 *
 * Revision 1.4  1998/04/24 02:43:19  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.3  1998/04/22 22:44:31  jyh
 * *** empty log message ***
 *
 * Revision 1.2  1998/04/21 19:54:42  jyh
 * Upgraded refiner for program extraction.
 *
 * Revision 1.1  1997/08/06 16:18:18  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 *)

include Tactic_type

open Printf
open Debug

open Term
open Term_table
open Refine_sig
open Resource

open Tactic_type

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
         try lookup tbl t with
            Not_found ->
               raise (RefineError (StringTermError ("typeinf: can't infer type for", t)))
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
let typeinf_of_proof { tac_arg = { ref_rsrc = { ref_typeinf = inf } } } = inf

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
