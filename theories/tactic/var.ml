(*
 * NEw variable generation.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 * 
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)

open Refiner.Refiner.Term
open Refiner.Refiner.RefineError

open Printf
open Nl_debug
open Ctype

open Sequent
open Tactic_type

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
      if len = 0 then
         v, 0
      else
         let rec search i =
            if i = 0 then
               v, 0
            else if is_digit v.[i - 1] then
               search (i - 1)
            else if i = len then
               v, 0
            else
               String.sub v 0 i, int_of_string (String.sub v i (len - i))
         in
            search len

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
