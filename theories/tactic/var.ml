(*!
 * @spelling{var vars productElimination}
 *
 * @begin[doc]
 * @theory[Var]
 *
 * The @tt{Var} module provides utilities to
 * generate new variables that are guaranteed to be distinct
 * from all other bound variables in a proof goal.  For example,
 * the @tt{productElimination} (Section @reftheory[Itt_dprod])
 * rule, splits a hypothesis of the form $x@colon T_1 @times T_2$
 * into two hypotheses $u@colon T_1$ and $v@colon T_2$.  The variables
 * $u$ and $v$ have to be chosen at rule application time, and this
 * module assists in the generation of new names.
 *
 * There are three basic functions implemented here.
 * @begin[verbatim]
 * val new_var         : string -> string list -> string
 * val maybe_new_var   : string -> string list -> string
 * val maybe_new_vars  : string list -> string list -> string list
 * @end[verbatim]
 *
 * The function $@tt[new_var]@space v@space @i{vars}$ generates a new variable
 * ``similar'' to $v$, but not contained in $@i{vars}$.  In this
 * case ``similar'' means that the variable has the same name, but
 * it may have a numerical suffix to make it distinct.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 *
 * This file is part of MetaPRL, a modular, higher order
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
 * @email{jyh@cs.caltech.edu}
 *
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
extends Summary
(*! @docoff *)

open Refiner.Refiner.Term
open Refiner.Refiner.RefineError

open Printf
open Mp_debug
open String_util

open Tactic_type

(*
 * Debug statement.
 *)
let _ =
   show_loading "Loading Var%t"

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
let mem' vars v = List.mem v vars

let new_var v vars =
   String_util.vnewname (fst (split_var v)) (mem' vars)

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

let maybe_new_vars_array =
   let rec search_simple bound_vars vars i length =
      if i = length then
         vars
      else
         let v = vars.(i) in
            if List.mem v bound_vars then
               let vars = Array.copy vars in
                  vars.(i) <- new_var v bound_vars;
                  search_found bound_vars vars (succ i) length
            else
               search_simple (v :: bound_vars) vars (succ i) length
   and search_found bound_vars vars i length =
      if i = length then
         vars
      else
         let v = vars.(i) in
            if List.mem v bound_vars then
               let v = new_var v bound_vars in
                  vars.(i) <- v;
                  search_found (v :: bound_vars) vars (succ i) length
            else
               search_found (v :: bound_vars) vars (succ i) length
   in
      (fun p vars ->
            search_simple (Sequent.declared_vars p) vars 0 (Array.length vars))

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

let maybe_new_vars6 p v1 v2 v3 v4 v5 v6 =
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
   let vars = v5 :: vars in
   let v6 = maybe_new_var v6 vars in
      v1, v2, v3, v4, v5, v6

let maybe_new_vars7 p v1 v2 v3 v4 v5 v6 v7 =
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
   let vars = v5 :: vars in
   let v6 = maybe_new_var v6 vars in
   let vars = v6 :: vars in
   let v7 = maybe_new_var v7 vars in
      v1, v2, v3, v4, v5, v6, v7

let maybe_new_vars8 p v1 v2 v3 v4 v5 v6 v7 v8 =
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
   let vars = v5 :: vars in
   let v6 = maybe_new_var v6 vars in
   let vars = v6 :: vars in
   let v7 = maybe_new_var v7 vars in
   let vars = v7 :: vars in
   let v8 = maybe_new_var v8 vars in
      v1, v2, v3, v4, v5, v6, v7, v8

let maybe_new_vars9 p v1 v2 v3 v4 v5 v6 v7 v8 v9 =
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
   let vars = v5 :: vars in
   let v6 = maybe_new_var v6 vars in
   let vars = v6 :: vars in
   let v7 = maybe_new_var v7 vars in
   let vars = v7 :: vars in
   let v8 = maybe_new_var v8 vars in
   let vars = v8 :: vars in
   let v9 = maybe_new_var v9 vars in
      v1, v2, v3, v4, v5, v6, v7, v8, v9

(*
 * Optional vars.
 *)
let get_opt_var_arg v p =
   try dest_var (Sequent.get_term_arg p "var") with
      RefineError _ ->
         maybe_new_var v (Sequent.declared_vars p)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
