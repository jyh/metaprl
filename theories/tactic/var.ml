(*
 * NEw variable generation.
 *)

open Printf
open Debug
open Ctype

open Sequent

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
         String_util.sub "Var.split_var" v 0 !i, int_of_string (String_util.sub "Var.split_var" v !i (len - !i))

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

let maybe_new_vars1 p v1 =
   let vars = Sequent.declared_vars p in
      maybe_new_var v1 vars

let maybe_new_vars2 p v1 v2 =
   let vars = Sequent.declared_vars p in
   let v1 = maybe_new_var v1 vars in
   let vars = v1 :: vars in
   let v2 = maybe_new_var v2 vars in
      v1, v2

let maybe_new_vars3 p v1 v2 v3 =
   let vars = Sequent.declared_vars p in
   let v1 = maybe_new_var v1 vars in
   let vars = v1 :: vars in
   let v2 = maybe_new_var v2 vars in
   let vars = v2 :: vars in
   let v3 = maybe_new_var v3 vars in
      v1, v2, v3

let maybe_new_vars4 p v1 v2 v3 v4 =
   let vars = Sequent.declared_vars p in
   let v1 = maybe_new_var v1 vars in
   let vars = v1 :: vars in
   let v2 = maybe_new_var v2 vars in
   let vars = v2 :: vars in
   let v3 = maybe_new_var v3 vars in
   let vars = v3 :: vars in
   let v4 = maybe_new_var v4 vars in
      v1, v2, v3, v4

let maybe_new_vars5 p v1 v2 v3 v4 v5 =
   let vars = Sequent.declared_vars p in
   let v1 = maybe_new_var v1 vars in
   let vars = v1 :: vars in
   let v2 = maybe_new_var v2 vars in
   let vars = v2 :: vars in
   let v3 = maybe_new_var v3 vars in
   let vars = v3 :: vars in
   let v4 = maybe_new_var v4 vars in
   let vars = v4 :: vars in
   let v5 = maybe_new_var v5 vars in
      v1, v2, v3, v4, v5

(*
 * $Log$
 * Revision 1.5  1998/06/16 16:26:25  jyh
 * Added itt_test.
 *
 * Revision 1.4  1998/06/15 22:33:51  jyh
 * Added CZF.
 *
 * Revision 1.3  1998/06/03 22:20:06  jyh
 * Nonpolymorphic refiner.
 *
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
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
