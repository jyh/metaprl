(*
 * NEw variable generation.
 *)

open Refiner.Refiner.Term
open Refiner.Refiner.RefineError

open Printf
open Debug
open Ctype

open Sequent
open Tacticals

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
 * Optional vars.
 *)
let get_opt_var_arg v p =
   try dest_var (get_term_arg p "var") with
      RefineError _ ->
         maybe_new_var v (declared_vars p)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
