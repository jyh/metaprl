(*
 * NEw variable generation.
 *
 * $Log$
 * Revision 1.2  1998/04/24 02:44:07  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.1  1997/04/28 15:52:45  jyh
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
 * Revision 1.1  1996/09/25 22:52:07  jyh
 * Initial "tactical" commit.
 *
 *)

open Printf
open Debug
open Ctype

(*
 * Debug statement.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Var%t" eflush

(*
 * Split a varname into root, suffix
 * according to the pattern %s%d
 *)
let split_var v =
   let len = String.length v in
   let i = ref (len - 1) in
      while !i <> 0 & is_digit v.[!i] do
         decr i
      done;
      if !i = 0 then
         v, 0
      else
         String.sub v 0 !i, int_of_string (String.sub v !i (len - !i))

(*
 * Generate a new variable disjoint from the given vars.
 * If the var has a name matching "%s%d", then keep the same form
 * and use the smallest index to keep the var name disjoint.
 *)
let new_var v vars =
   let root, _ = split_var v in
   let rec aux i =
      let newv = root ^ (string_of_int i) in
         if List.mem newv vars then
            aux (i + 1)
         else
            newv
   in
      aux 1

let maybe_new_var v vars =
   if List.mem v vars then
      new_var v vars
   else
      v

let maybe_new_vars vars vars' =
   let rec aux l l' = function
      h::t ->
         let h' = maybe_new_var h l in
            aux (h'::l) (h'::l') t
    | [] -> l'
   in
      aux vars' [] vars

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
