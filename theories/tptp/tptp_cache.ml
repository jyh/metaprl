(*
 * Create tables for success/failure/cycle-detection
 * classes.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
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
open Lm_debug
open Lm_printf
open Lm_symbol
open Lm_string_set

open Term_sig
open Refiner.Refiner.TermType
open Refiner.Refiner.Term

let debug_cache =
   create_debug (**)
      { debug_name = "cache";
        debug_description = "Show TPTP cache operations";
        debug_value = false
      }

(************************************************************************
 * COMPATIBILITY
 ************************************************************************)

let dest_var t =
   string_of_symbol (dest_var t)

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * This type is used for comparing terms.
 *)
type comparison =
   LessThan
 | GreaterThan
 | Equal of (string * string) list

(*
 * The subsumed exception is raised when a clause
 * is already in the cache.
 *)
exception Subsumed

(************************************************************************
 * TERM TABLE                                                           *
 ************************************************************************)

(*
 * Second value in the association list.
 *)
let rec rev_assoc v = function
   (v1, v2) :: subst ->
      if v = v2 then
         v1
      else
         rev_assoc v subst
 | [] ->
      raise Not_found

(*
 * This compares clauses, where all variables are
 * free.  Terms are sorted from the more general to
 * the less general.  This acts a little like unification,
 * but we just match variables.
 *)
let rec compare_terms constantp subst term1 term2 =
   if is_var_term term1 then
      if is_var_term term2 then
         let v1 = dest_var term1 in
         let v2 = dest_var term2 in
            if constantp v1 then
               if v2 = v1 then
                  Equal subst
               else if constantp v2 then
                  if v1 < v2 then
                     LessThan
                  else
                     GreaterThan
               else
                  GreaterThan
            else if constantp v2 then
               LessThan
            else
               compare_vars subst v1 v2
      else
         LessThan
   else if is_var_term term2 then
      GreaterThan
   else
      let trm1 = dest_term term1 in
      let trm2 = dest_term term2 in
         match Stdlib.compare trm1.term_op trm2.term_op with
            0 ->
               compare_bterm_lists constantp subst trm1.term_terms trm2.term_terms
          | ord ->
               if ord > 0 then
                  GreaterThan
               else
                  LessThan

and compare_bterm_lists constantp subst terms1 terms2 =
   match terms1, terms2 with
      term1 :: terms1, term2 :: terms2 ->
         begin
            match compare_terms constantp subst (dest_simple_bterm term1) (dest_simple_bterm term2) with
               Equal subst ->
                  compare_bterm_lists constantp subst terms1 terms2
             | ord ->
                  ord
         end
    | [], [] ->
         Equal subst
    | [], _ ->
         LessThan
    | _, [] ->
         GreaterThan

and compare_term_lists constantp subst terms1 terms2 =
   match terms1, terms2 with
      term1 :: terms1, term2 :: terms2 ->
         begin
            match compare_terms constantp subst term1 term2 with
               Equal subst ->
                  compare_term_lists constantp subst terms1 terms2
             | ord ->
                  ord
         end
    | [], [] ->
         Equal subst
    | [], _ ->
         LessThan
    | _, [] ->
         GreaterThan

and compare_vars subst v1 v2 =
   try
      let v2' = List.assoc v1 subst in
      let ord = Stdlib.compare v2 v2' in
         if ord = 0 then
            Equal subst
         else if ord < 0 then
            LessThan
         else
            GreaterThan
   with
      Not_found ->
         try
            let v1' = rev_assoc v2 subst in
               if v1 < v1' then
                  LessThan
               else
                  GreaterThan
         with
            Not_found ->
               Equal ((v1, v2) :: subst)

(*
 * See if one list is a sublist of the other.
 * Clauses are always sorted.
 *)
let rec compare_term_sub_list constantp subst terms1 terms2 =
   match terms1, terms2 with
      term1 :: terms1', term2 :: terms2' ->
         begin
            match compare_terms constantp subst term1 term2 with
               Equal subst ->
                  compare_term_sub_list constantp subst terms1' terms2'
             | LessThan ->
                  (*
                   * The first list contains a term not in the
                   * second list.  It may be subsumed.
                   *)
                  compare_term_sub_list constantp subst terms1' terms2
             | GreaterThan ->
                  (*
                   * The first list does not contain a term in
                   * the second list, so its not a sublist.
                   *)
                  false
         end
    | [], []
    | _, [] ->
         true
    | [], _ ->
         false

(*
 * Sort a list of terms.
 * All variables are treated as constant.
 *)
let sort_term_list terms =
   let compare term1 term2 =
      match compare_terms (fun v -> true) [] term1 term2 with
         LessThan ->
            true
       | GreaterThan
       | Equal _ ->
            false
   in
      Sort.list compare terms

(*
 * Merge two term lists, and remove duplicates.
 * All variables are treated as constants.
 * The two lists have had a substitution performed on
 * them, so they may not quite be in sorted order, but
 * a bubble sort will be probably be faster than
 * a quicksort.
 *)
let merge_term_lists =
   (*
    * All variables are treated as constants.
    *)
   let merge_compare = compare_terms (fun v -> true) [] in

   (*
    * Bubble function.
    *)
   let rec insert term = function
      term' :: terms ->
         begin
            match merge_compare term term' with
               Equal _ ->
                  term' :: terms
             | LessThan ->
                  term :: term' :: terms
             | GreaterThan ->
                  term' :: insert term terms
         end
    | [] ->
         [term]
   in

   (*
    * Bubble sort.
    *)
   let rec merge_term_lists_aux terms terms1 terms2 =
      match terms1, terms2 with
         term1 :: terms1', term2 :: terms2' ->
            begin
               match merge_compare term1 term2 with
                  Equal _ ->
                     merge_term_lists_aux (insert term1 terms) terms1' terms2'
                | LessThan ->
                     merge_term_lists_aux (insert term1 terms) terms1' terms2
                | GreaterThan ->
                     merge_term_lists_aux (insert term2 terms) terms1 terms2'
            end
       | term1 :: terms1, [] ->
            merge_term_lists_aux (insert term1 terms) terms1 []
       | [], term2 :: terms2 ->
            merge_term_lists_aux (insert term2 terms) terms2 []
       | [], [] ->
            terms
   in
      merge_term_lists_aux []

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

module TermCompare =
struct
   type t = term

   let compare = Stdlib.compare
end

module TermTable = Lm_map.LmMakeList (TermCompare)

module TptpCache =
struct
   (*
    * A cache is a term cache.
    *)
   type t =
      { cache_constants : string -> bool;
        cache_table : term list TermTable.t
      }

   let create constants =
      let is_constant = StringSet.mem constants in
         { cache_constants = is_constant;
           cache_table = TermTable.empty
         }

   (*
    * Check if a clause is subsumed by an existing entry.
    * Check each part of the clause.  Remember clauses
    * by pointer equality.
    *)
   let rec subsumed_goals constants memo clause = function
      goal :: goals ->
         if List.memq goal memo then
            subsumed_goals constants memo clause goals
         else if compare_term_sub_list constants [] clause goal then
            raise Subsumed
         else
            subsumed_goals constants (goal :: memo) clause goals
    | [] ->
         memo

   let rec subsumed constants memo find_all clause = function
      term :: terms ->
         let memo =
            try
               let goals = find_all term in
                  subsumed_goals constants memo clause goals
            with
               Not_found ->
                  memo
         in
            subsumed constants memo find_all clause terms
    | [] ->
         ()

   (*
    * See if a goal is subsumed.
    *)
   let subsumed t clause =
      if !debug_cache then
         eprintf "Tptp_cache.subsumed: %a%t" print_term_list clause eflush;
      let flag =
         try
            let find_all = TermTable.find_all t.cache_table in
               subsumed t.cache_constants [] find_all clause clause;
               false
         with
            Subsumed ->
               true
      in
         if !debug_cache then
            eprintf "Tptp_cache.subsumed: %b%t" flag eflush;
         flag

   (*
    * Add a goal to the table, unless it is subsumed by
    * and existing entry.
    *)
   let rec add_clause clause add t = function
      term :: terms ->
         add_clause clause add (add t term clause) terms
    | [] ->
         t

   let insert t clause =
      { t with cache_table = add_clause clause TermTable.add t.cache_table clause }
end

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
