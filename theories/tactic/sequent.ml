(*
 * Utilities for tactics.
 *
 * ----------------------------------------------------------------
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
 * jyh@cs.cornell.edu
 *)

open Printf
open Mp_debug

open Refiner.Refiner
open Refiner.Refiner.TermType
open Refiner.Refiner.Refine

(*
 * Debug statement.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Sequent%t" eflush

(*
 * Types.
 *)
type extract = Tactic_type.extract
type tactic = Tactic_type.tactic
type tactic_arg = Tactic_type.tactic_arg
type tactic_value = Tactic_type.tactic_value
type cache = Tactic_type.cache
type raw_cache = Tactic_type.raw_cache
type sentinal = Tactic_type.sentinal
type 'a attributes = 'a Tactic_type.attributes
type raw_attribute = Tactic_type.raw_attribute
type raw_attributes = Tactic_type.raw_attributes

(*
 * Construction.
 *)
let create = Tactic_type.create

(*
 * Sentinals.
 *)
let sentinal_of_refiner = Tactic_type.sentinal_of_refiner
let sentinal_of_refiner_object = Tactic_type.sentinal_of_refiner_object

(*
 * Cache.
 *)
let make_cache = Tactic_type.make_cache
let cache = Tactic_type.cache

(*
 * Two tactic_arguments are equal when they have
 * equal msequent parts.  Their labels, etc, are
 * not compared.
 *)
let tactic_arg_alpha_equal = Tactic_type.tactic_arg_alpha_equal

(*
 * Addressing.
 *)
let goal = Tactic_type.goal

let msequent = Tactic_type.msequent

let concl arg =
   Tactic_type.nth_concl arg 1

let label = Tactic_type.label

let args p =
   let { sequent_args = args } = TermMan.explode_sequent (goal p) in
      TermMan.dest_xlist args

(*
 * Sequent parts.
 *)
let hyp_count arg =
   TermMan.num_hyps (goal arg)

let hyp_count_addr arg =
   let goal = goal arg in
      TermMan.hyp_range_addr goal (TermMan.num_hyps goal)

let hyp_split_addr arg i =
   let goal = goal arg in
   let count = TermMan.num_hyps goal in
   let j, k =
      if i < 0 then
         count + i + 1, (-1) - i
      else
         i, count - i
   in
      TermMan.hyp_range_addr goal j, TermMan.hyp_range_addr goal k

let hyp_indices arg i =
   let goal = goal arg in
   let count = TermMan.num_hyps goal in
   let j, k =
      if i < 0 then
         count + i, (-1) - i
      else
         i - 1, count - i
   in
      TermMan.hyp_range_addr goal j, TermMan.hyp_range_addr goal k

let get_pos_hyp_num arg i =
   if i < 0 then
      (hyp_count arg) + i + 1
   else
      i

let nth_hyp p i =
   Tactic_type.nth_hyp p (get_pos_hyp_num p i)

let clause_addr p i =
   TermMan.nth_clause_addr (goal p) (get_pos_hyp_num p i)

let get_decl_number arg v =
   TermMan.get_decl_number (goal arg) v

let declared_vars arg =
   let seq = msequent arg in
   let vars, goal, _ = dest_msequent_vars seq in
      vars @ (TermMan.declared_vars goal)

let explode_sequent arg =
   TermMan.explode_sequent (goal arg)

let is_free_seq_var i v p =
   TermMan.is_free_seq_var (get_pos_hyp_num p i) v (goal p)

(*
 * Modification of the argument.
 * These are functional.
 *)
let set_goal  = Tactic_type.set_goal
let set_concl = Tactic_type.set_concl
let set_label = Tactic_type.set_label

(*
 * Attribute construction.
 *)
let term_attribute       = Tactic_type.term_attribute
let type_attribute       = Tactic_type.type_attribute
let int_attribute        = Tactic_type.int_attribute
let bool_attribute       = Tactic_type.bool_attribute
let subst_attribute      = Tactic_type.subst_attribute
let conv_attribute       = Tactic_type.conv_attribute
let tactic_attribute     = Tactic_type.tactic_attribute
let int_tactic_attribute = Tactic_type.int_tactic_attribute
let arg_tactic_attribute = Tactic_type.arg_tactic_attribute
let tsubst_attribute     = Tactic_type.tsubst_attribute
let typeinf_attribute    = Tactic_type.typeinf_attribute

(*
 * Argument functions.
 *)
let attributes         = Tactic_type.attributes
let get_term_arg       = Tactic_type.get_term
let get_type_arg       = Tactic_type.get_type
let get_int_arg        = Tactic_type.get_int
let get_bool_arg       = Tactic_type.get_bool
let get_subst_arg      = Tactic_type.get_subst
let get_conv_arg       = Tactic_type.get_conv
let get_tactic_arg     = Tactic_type.get_tactic
let get_int_tactic_arg = Tactic_type.get_int_tactic
let get_arg_tactic_arg = Tactic_type.get_arg_tactic
let get_tsubst_arg     = Tactic_type.get_tsubst
let get_typeinf_arg    = Tactic_type.get_typeinf

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
