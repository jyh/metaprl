(*
 * The D tactic performs a case selection on the conclusion opname.
 *)

open Printf
open Debug

open Opname
open Refiner.Refiner.Term
open Refiner.Refiner.TermAddr
open Refiner.Refiner.Refine
open Resource
open Simple_print

open Tactic_type
open Sequent

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Base_dtactic%t" eflush

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * The data type for the D tactic maps opname to
 * a tactic.
 *
 * The key is on the operator name and the arities of the subterms.
 *)
type key = opname * int list

type d_data =
   { d_info : (key * (int -> tactic)) list;
     mutable d_table : (key, int -> tactic) Hashtbl.t option
   }

resource (term * (int -> tactic), int -> tactic, d_data) d_resource

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Check if the first list is a suffix of the other.
 *)
let check_suffix list1 =
   let rec aux l =
      if list1 == l then
         true
      else
         match l with
            _::t ->
               aux t
          | [] ->
               false
   in
      aux

(*
 * Insert the first list into the second.
 *)
let rec insert_data data1 = function
   h::t ->
      begin
         match h with
            name, tac ->
               begin
                  try 
                     List.assq name data1;
                     insert_data data1 t
                  with
                     Not_found ->
                        insert_data (h::data1) t
               end
      end
      
 | [] -> data1
            
(*
 * Join the data from two bases.
 * First check if one is a suffix of the other.
 * This will commonly be the case, and so we optimize it.
 *)
let join_data base1 base2 =
   let data1 = base1.d_info in
   let data2 = base2.d_info in
      if check_suffix data1 data2 then
         base2
      else if check_suffix data2 data1 then
         base1
      else
         { d_info = insert_data data2 data1; d_table = None }

(*
 * Compute the hashtable from the info.
 *)
let compute_table info =
   let tbl = Hashtbl.create (List.length info) in
   let aux (key, tac) =
      Hashtbl.add tbl key tac
   in
      List.iter aux info;
      tbl

(*
 * Extract a D tactic from the data.
 * The tactic checks for an optable.
 *)
let extract_data base =
   let d i p =
      let tbl =
         (* Compute the hashtbl if necessary *)
         match base.d_table with
            None ->
               let tbl = compute_table base.d_info in
                  base.d_table <- Some tbl;
                  tbl
          | Some tbl -> tbl
      in
      let t =
         (* Get the term described by the number *)
         if i = 0 then
            concl p
         else
            nth_hyp i p
      in
      let key = opname_of_term t, subterm_arities t in
         try
            (* Find and apply the right tactic *)
            let tac = Hashtbl.find tbl key in
               tac i p
         with
            Not_found ->
               raise (RefineError (StringError ("D tactic doesn't know about " ^ (string_of_opname (fst key)))))
   in
      d

(*
 * Add a new tactic.
 *)
let improve_data (t, tac) data =
   { d_info = ((opname_of_term t, subterm_arities t), tac)::(data.d_info);
     d_table = None
   }

(*
 * Wrap up the joiner.
 *)
let rec join_resource base1 base2 =
   let data = join_data base1.resource_data base2.resource_data in
      { resource_data = data;
        resource_join = join_resource;
        resource_extract = extract_resource;
        resource_improve = improve_resource
      }
      
and extract_resource { resource_data = data } =
   extract_data data
   
and improve_resource { resource_data = data } x =
   { resource_data = improve_data x data;
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

(*
 * Resource.
 *)
let d_resource =
   { resource_data = { d_info = []; d_table = None };
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

let dT = d_resource.resource_extract d_resource

(*
 * $Log$
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
