(*
 * Utilities for tactics.
 *)

open Printf
open Nl_debug

open Refiner.Refiner
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
type tactic_arg = Tactic_type.tactic_arg
type tactic_value = Tactic_type.tactic_value
type cache = Tactic_type.cache
type 'a attributes = 'a Tactic_type.attributes

(*
 * Construction.
 *)
let create = Tactic_type.create

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
   Tactic_type.nth_concl arg 0

let cache = Tactic_type.cache

let label = Tactic_type.label

let attributes = Tactic_type.attributes

(*
 * Sequent parts.
 *)
let hyp_count arg =
   TermMan.num_hyps (goal arg)

let hyp_indices arg i =
   let count = hyp_count arg in
      if i < 0 then
         count + i, (-1) - i
      else
         i - 1, count - i

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
 * Argument functions.
 *)
let get_term_arg       = Tactic_type.get_term
let get_type_arg       = Tactic_type.get_type
let get_int_arg        = Tactic_type.get_int
let get_bool_arg       = Tactic_type.get_bool
let get_subst_arg      = Tactic_type.get_subst
let get_tactic_arg     = Tactic_type.get_tactic
let get_int_tactic_arg = Tactic_type.get_int_tactic
let get_arg_tactic_arg = Tactic_type.get_arg_tactic
let get_typeinf_arg    = Tactic_type.get_typeinf

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
