(*
 * This is the proof procedure for TPTP.
 * The following procedure is not so efficient, but
 * we are mainly using it for performance analysis.
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

extends Tptp_load

open Printf
open Mp_debug
open String_set
open Thread_util

open Refiner.Refiner
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermShape
open Refiner.Refiner.RefineError

open Unify_mm

open Tactic_type
open Tactic_type.Tacticals

open Base_dtactic

open Itt_equal
open Itt_struct
open Itt_atom
open Itt_logic
open Itt_rfun

open Tptp
open Tptp_cache

let debug_tptp =
   create_debug (**)
      { debug_name = "tptp";
        debug_description = "show TPTP tactic operations";
        debug_value = false
      }

let debug_tptp_prove =
   create_debug (**)
      { debug_name = "tptp_prove";
        debug_description = "show TPTP proof steps";
        debug_value = false
      }

let debug_subst = load_debug "subst"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Just create a rule to duplicate the goal for testing.
 *)
interactive duplicate :
   sequent ['ext] { 'H >- 'T } -->
   sequent ['ext] { 'H >- 'T } -->
   sequent ['ext] { 'H >- 'T }

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * Keep a list of the hyps in exploded form.
 *    the positive vars are the head constants
 *       of the positive disjuncts in the clause,
 *    the negative vars are the head constants
 *       of the negative disjuncts.
 *)
type tptp_clause_info =
   { tptp_vars : string list;
     tptp_body : term list;
     tptp_positive : StringSet.t;
     tptp_negative : StringSet.t
   }

(*
 * This is the global info needed during the proof.
 *    The first_hyp is the index of the first hyp that
 *    is a clause (and not a typeing assumption).
 *
 *    The constants are the function and predicate symbols.
 *
 *    The hyps are saved in exploded form.
 *)
type tptp_info =
   { tptp_first_hyp : int;
     tptp_constants : StringSet.t;
     tptp_hyps : tptp_clause_info array;
     tptp_fail_cache : TptpCache.t ref;
     tptp_bound : int
   }

(*
 * During proof, we keep the set of goals that we
 * are currently exploring.  If the same goal occurs,
 * we abort the cycle.
 *
 * The level is the current depth of the search.
 *
 * The info is the constant info about the problem
 * being explored.
 *)
type t =
   { tptp_goal_cache : TptpCache.t;
     tptp_goal : tptp_clause_info;
     tptp_level : int;
     tptp_info : tptp_info
   }

(************************************************************************
 * UTILITIES                                                            *
 ************************************************************************)

(*
 * Tabbing for printing.
 *)
let tab out i =
   for j = 0 to i do
      output_char out ' '
   done

(*
 * Print a substitution.
 *)
let print_subst out =
   let print (v, t) =
      fprintf out " %s=%a" v print_term t
   in
      List.iter print

(*
 *   Print equnlist
 *)
let print_eqnlist out =
   let print (t1, t2) =
      fprintf out " %a=%a" print_term t1 print_term t2
   in
      List.iter print

let print_unify_eqnlist out eqnl =
   print_eqnlist out (eqnlist2ttlist   eqnl)

(************************************************************************
 * TERM SET                                                             *
 ************************************************************************)

(*
 * We first do some preprocessing on the sequent to figure
 * which hypotheses are just declarations.
 *)
let decl_opnames =
   List.map opname_of_term (**)
      [<< atom0 >>;
       << atom1 >>;
       << atom2 >>;
       << atom3 >>;
       << atom4 >>;
       << atom5 >>;
       << prop0 >>;
       << prop1 >>;
       << prop2 >>;
       << prop3 >>;
       << prop4 >>;
       << prop5 >>]

let rec first_clause_aux i len constants hyps =
   if i = len then
      i, constants
   else
      match SeqHyp.get hyps i with
         Hypothesis (v, hyp) ->
            let opname = opname_of_term hyp in
               if List.exists (Opname.eq opname) decl_opnames then
                  first_clause_aux (i + 1) len (StringSet.add constants v) hyps
               else
                  i, constants
       | Context _ ->
            first_clause_aux (i + 1) len constants hyps

let first_clause hyps =
   first_clause_aux 0 (SeqHyp.length hyps) StringSet.empty hyps

(*
 * Figure out which atoms are positive,
 * which are negative.
 *)
let split_atoms =
   let rec collect positive negative = function
      term :: terms ->
         if is_not_term term then
            let term = dest_not term in
            let v = dest_var (head_of_apply term) in
               collect positive (StringSet.add negative v) terms
         else
            let v = dest_var (head_of_apply term) in
               collect (StringSet.add positive v) negative terms
    | [] ->
         positive, negative
   in
      collect StringSet.empty StringSet.empty

(*
 * Spread the clause.
 *)
let dest_hyp t =
   let vars, body = dest_all t in
   let body = dest_or body in
   let positive, negative = split_atoms body in
      { tptp_vars = vars;
        tptp_body = sort_term_list body;
        tptp_negative = negative;
        tptp_positive = positive
      }

let dest_hyps bound hyps =
   let j, constants = first_clause hyps in
   let len = SeqHyp.length hyps in
   let null_hyp =
      { tptp_vars = [];
        tptp_body = [];
        tptp_negative = StringSet.empty;
        tptp_positive = StringSet.empty
      }
   in
   let hyps' = Array.create len null_hyp in
   let _ =
      for i = j to len - 1 do
         match SeqHyp.get hyps i with
            Hypothesis (_, hyp) ->
               hyps'.(i) <- dest_hyp hyp
          | Context _ ->
               ()
      done
   in
      { tptp_first_hyp = j;
        tptp_constants = constants;
        tptp_hyps = hyps';
        tptp_fail_cache = ref (TptpCache.create constants);
        tptp_bound = bound
      }

(*
 * Break apart a goal clause.
 *)
let dest_goal t =
   let vars, body = dest_exists t in
   let body = sort_term_list (dest_and body) in
   let positive, negative = split_atoms body in
      { tptp_vars = vars;
        tptp_body = body;
        tptp_positive = positive;
        tptp_negative = negative
      }

(************************************************************************
 * UNIFICATION                                                          *
 ************************************************************************)

(*
 * Unify the term with as many terms in the list
 * as possible.  Return the unifier, and the
 * list of terms that did not match.
 *)
let rec unify_term_list foundp eqnl constants term1 = function
   term2 :: terms2 ->
      begin
         try
            if !debug_tptp then
               eprintf "Unifying terms:\n\tTerm1: %a\n\tTerm2: %a\n\tConstants: %a\n\tSubst: %a%t" (**)
                  print_term term1
                  print_term term2
                  print_string_list (StringSet.elements constants)
                  print_unify_eqnlist eqnl
                  eflush;
            let eqnl = unify_eqnl_eqnl (eqnlist_append_eqn eqnl term1 term2) constants in
               if !debug_tptp then
                  eprintf "Unification:%a%t" (**)
                     print_unify_eqnlist eqnl
                     eflush;
               unify_term_list true eqnl constants term1 terms2
         with
           RefineError _ ->
               if !debug_tptp then
                  eprintf "Unification failed%t" eflush;
               let eqnl, terms2 = unify_term_list foundp eqnl constants term1 terms2 in
                  eqnl, term2 :: terms2
      end
 | [] ->
      if foundp then
         eqnl, []
      else
         raise (RefineError ("unify", StringError "terms do not unify"))

(*
 * Given two term lists to be unified,
 * find a unifier.  Return the unifier,
 * and the remainders of the term lists.
 *
 * In this version we return a single unifier for
 * the leftmost unification.
 *)
let rec unify_term_lists constants terms1 terms2 =
   match terms1 with
      term1 :: terms1 ->
         begin
            try
               let subst, terms2 = unify_term_list false eqnlist_empty constants term1 terms2 in
                  try
                     let subst, terms1 = unify_term_list true subst constants term1 terms1 in
                        subst, terms1, terms2
                  with
                     RefineError _ ->
                        subst, terms1, terms2
            with
               RefineError _ ->
                  let subst, terms1, terms2 = unify_term_lists constants terms1 terms2 in
                     subst, term1 :: terms1, terms2
         end
    | [] ->
         raise (RefineError ("unify", StringError "terms do not unify"))

let unify_term_lists constants terms1 terms2 =
   let eqnl, terms1, terms2 = unify_term_lists constants terms1 terms2 in
      (unify_eqnl eqnl constants), terms1, terms2

(*
 * Check that the goal and the hyp have some hope at unification.
 *)
let check_unify
    { tptp_positive = pos1; tptp_negative = neg1 }
    { tptp_positive = pos2; tptp_negative = neg2 } =
   if not (StringSet.intersectp pos1 pos2 || StringSet.intersectp neg1 neg2) then
      raise (RefineError ("unify", StringError "terms do not unify"))

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Double-negation elimination.
 *)
let negate_term t =
   if is_not_term t then
      dest_not t
   else
      mk_not_term t

(*
 * New variable from an index.
 *)
let rec new_vars varcount l vars i =
   if i = 0 then
      l
   else
      let v = "Y" ^ string_of_int varcount in
         if List.mem v vars then
            new_vars (varcount + 1) l vars i
         else
            new_vars (varcount + 1) (v :: l) vars (i - 1)

(*
 * Substitute recursively.
 *)
let rec expand subst term =
   match subst with
      (v, t) :: substs ->
         expand substs (subst1 term v t)
    | [] ->
         term

let expand_instance constants subst term =
   let term = expand subst term in
      if false && is_var_term term && not (StringSet.mem constants (dest_var term)) then
         t_term
      else
         term

(*
 * Build the new goal after a unification.
 *)
let new_goal constants subst terms1 terms2 =
   let vars, terms = List.split subst in
   let terms1 = List.map (expand subst) terms1 in
   let terms2 = List.map (fun t -> expand subst (negate_term t)) terms2 in
   let body = merge_term_lists terms1 terms2 in
   let positive, negative = split_atoms body in
   let free_vars = StringSet.not_mem_filt constants (StringSet.elements (free_vars_terms body)) in
      if free_vars = [] then
         let info =
            { tptp_vars = [];
              tptp_body = body;
              tptp_positive = positive;
              tptp_negative = negative
            }
         in
            subst, info
      else
         let new_vars = new_vars 1 [] vars (List.length free_vars) in
         let new_vars_terms = List.map mk_var_term new_vars in
         let subst' = List.combine free_vars new_vars_terms in
         let _ =
            if !debug_tptp then
               begin
                  eprintf "Standardizing:\n\tTerms: %a\n\tSubst: %a%t" (**)
                     print_term_list body
                     print_subst (List.combine free_vars new_vars_terms)
                     eflush;
                  debug_subst := true
               end
         in
         let body = List.map (fun t -> TermSubst.subst t free_vars new_vars_terms) body in
         let _ =
            if !debug_tptp then
               begin
                  debug_subst := false;
                  eprintf "Standardized:\n\tTerms: %a%t" (**)
                     print_term_list body
                     eflush
               end
         in
         let info =
            { tptp_vars = new_vars;
              tptp_body = body;
              tptp_positive = positive;
              tptp_negative = negative
            }
         in
            subst @ subst', info

let mk_goal { tptp_vars = vars; tptp_body = body } =
   if body = [] then
      true_term
   else
      mk_exists_term vars (mk_and_term body)

(*
 * Prove well-formedness of a function.
 *)
let get_apply_var t =
   let t = head_of_apply t in
      if is_var_term t then
         dest_var t
      else
         raise (RefineError ("prove_wf", StringError "term is not an application"))

let rec prove_wf p =
   let goal = Sequent.concl p in
      if is_atomic_term goal then
         let t = dest_atomic goal in
            if is_t_term t then
               t_atomic p
            else
               let v = get_apply_var t in
               let _ =
                  if !debug_tptp then
                     eprintf "Tptp_prove.prove_wf: atomic %s%t" v eflush
               in
               let i = Sequent.get_decl_number p v in
                  (atomicT i thenT prove_wf) p
      else if is_type_term goal then
         let t = dest_type_term goal in
            if is_apply_term t then
               let v = get_apply_var t in
               let _ =
                  if !debug_tptp then
                     eprintf "Tptp_prove.prove_wf: type %s%t" v eflush
               in
               let i = Sequent.get_decl_number p v in
                  (typeT i thenT prove_wf) p
            else
               (dT 0 thenT prove_wf) p
      else
         raise (RefineError ("prove_wf", StringTermError ("goal not recognized", goal)))

(*
 * Try the clause with the negation of the current clause.
 *)
let rec neg_trivial i j p =
   if !debug_tptp then
      eprintf "Tptp_prove.neg_trivial: %d %d%t" i j eflush;
   if j < 0 then
      raise (RefineError ("neg_trivial", StringError "match not found"))
   else if j = i then
      neg_trivial i (j - 1) p
   else if j > i then
      ((dT i thenT nthHypT (j - 1)) orelseT neg_trivial i (j - 1)) p
   else
      ((dT i thenT nthHypT j) orelseT neg_trivial i (j - 1)) p

(*
 * Try the negation of the clause with the current clause.
 *)
let rec pos_trivial i j p =
   if !debug_tptp then
      eprintf "Tptp_prove.pos_trivial: %d %d%t" i j eflush;
   if j < 0 then
      raise (RefineError ("pos_trivial", StringError "match not found"))
   else if j = i then
      pos_trivial i (j - 1) p
   else if j > i then
      ((dT j thenT nthHypT i) orelseT pos_trivial i (j - 1)) p
   else
      ((dT j thenT nthHypT (i - 1)) orelseT pos_trivial i (j - 1)) p

(*
 * The clause at hyp i either proves the goal, or
 * it negates an existing hyp.
 *)
let goal_or_trivial i p =
   let hyp = Sequent.nth_hyp p i in
   let j = Sequent.hyp_count p in
      if !debug_tptp then
         eprintf "Tptp_prove.goal_or_trivial: %a%t" debug_print hyp eflush;
      if is_not_term hyp then
         (nthHypT i orelseT neg_trivial i j) p
      else
         (nthHypT i orelseT pos_trivial i j) p

(*
 * Every disjunct in the clause either
 * proves the goal, or it negates an asserted hyp.
 *)
let rec decompose_clause i p =
   if !debug_tptp then
      eprintf "Tptp_prove.decompose_clause%t" eflush;
   let hyp = Sequent.nth_hyp p i in
      if is_or_term hyp then
         (dT i thenLT [goal_or_trivial i;
                       decompose_clause i]) p
      else
         goal_or_trivial i p

(*
 * Instantiate the hyp with the substitution,
 *)
let rec instantiate_hyp constants subst i p =
   if !debug_tptp then
      eprintf "Tptp_prove.instantiate_hyp%t" eflush;
   let hyp = Sequent.nth_hyp p i in
      if is_all_term hyp then
         let v = var_of_all hyp in
         let t = expand_instance constants subst (mk_var_term v) in
            (withT t (dT i)
             thenLT [prove_wf;
                     instantiate_hyp constants subst (Sequent.hyp_count p + 1)]) p
      else
         decompose_clause i p

(*
 * The goal may follow directly from the assumptions.
 *)
let rec trivial_goal i n p =
   if i < n then
      raise (RefineError ("trivial_goal", StringError "no match"))
   else
      (nthHypT i orelseT trivial_goal (i - 1) n) p

(*
 * Decompose the goal.
 *)
let rec instantiate_goal constants subst i n p =
   if !debug_tptp then
      eprintf "Tptp_prove.instantiate_goal:%a %t" print_subst subst eflush;
   let goal = Sequent.concl p in
      if is_exists_term goal then
         let v = var_of_exists goal in
         let t = expand_instance constants subst (mk_var_term v) in
            (withT t (dT 0)
             thenLT [prove_wf;
                     instantiate_goal constants subst i n;
                     prove_wf]) p
      else if is_and_term goal then
         (dT 0 thenT instantiate_goal constants subst i n) p
      else
         (trivial_goal (Sequent.hyp_count p) n orelseT instantiate_hyp constants subst i) p

(*
 * Decompose the existential that has just been asserted.
 * Save the new vars that are created.
 *)
let rec decompose_exists arg p =
   if !debug_tptp then
      eprintf "Tptp_prove.decompose_exists%t" eflush;
   let i = Sequent.hyp_count p in
   let hyp = Sequent.nth_hyp p i in
      if is_exists_term hyp then
         (dT i thenT decompose_exists arg) p
      else if is_and_term hyp then
         (dT i thenT decompose_exists arg) p
      else
         let constants, subst, i, n = arg in
            instantiate_goal constants subst i n p

(*
 * Assert and decompose the new goal.
 *)
let assert_new_goal level constants subst hyp_index goal tac p =
   if !debug_tptp_prove then
      eprintf "%aresolveT %d -> %a%t" tab level hyp_index debug_print goal eflush;
   (assertT goal
    thenLT [tac;
            decompose_exists (constants, subst, hyp_index, Sequent.hyp_count p)]) p

(*
 * Main tactic to unify on a hyp.
 *)
let resolveT i p =
   let hyp = Sequent.nth_hyp p i in
   let { sequent_hyps = hyps; sequent_goals = goals } = Sequent.explode_sequent p in
   let j, constants = first_clause hyps in
   let hyp_info = dest_hyp hyp in
   let goal_info = dest_goal (SeqGoal.get goals 0) in
   let _ =
      if !debug_tptp then
         eprintf "Starting unification: constants %a%t" print_string_list (StringSet.elements constants) eflush
   in
   let subst, terms1, terms2 = unify_term_lists constants goal_info.tptp_body hyp_info.tptp_body in
   let subst, new_info = new_goal constants subst terms1 terms2 in
   let goal = mk_goal new_info in
      if !debug_tptp then
         eprintf "New goal %a%t" print_term goal eflush;
      assert_new_goal 0 constants subst i goal idT p

(************************************************************************
 * SEARCH                                                               *
 ************************************************************************)

(*
 * This just tests the marshaler on values.
 *)
let refine_count = ref 0
let fail_count = ref 0

let rec prove_auxT
    { tptp_goal_cache = goal_cache;
      tptp_goal = goal_info;
      tptp_level = level;
      tptp_info =
         { tptp_constants = constants;
           tptp_first_hyp = first_hyp;
           tptp_hyps = hyps;
           tptp_fail_cache = fail_cache;
           tptp_bound = bound
         } as info
    } p =
   match goal_info.tptp_body with
      [] ->
         dT 0 p
    | body ->
         if level > bound then
            raise (RefineError ("proveT", StringError "failed"));
(*
 * Turn off fail-cache for more determinstic performance
 * testing.  --jyh
         if TptpCache.subsumed !fail_cache body then
            raise (RefineError ("proveT", StringError "failed"));
 *)
         if TptpCache.subsumed goal_cache body then
            raise (RefineError ("proveT", StringError "cycle detected"));
         let cache = TptpCache.insert goal_cache body in
         let nextT goal_info =
            prove_auxT (**)
               { tptp_goal_cache = cache;
                 tptp_goal = goal_info;
                 tptp_level = level + 1;
                 tptp_info = info
               }
         in
         let count = Sequent.hyp_count p in
         let rec find_hyp i =
            if i = count then
               begin
                  incr fail_count;
                  fail_cache := TptpCache.insert !fail_cache body;
                  raise (RefineError ("proveT", StringError "failed"))
               end
            else
               try
                  let hyp_info = hyps.(i - 1) in
                  (* let _ = check_unify hyp_info goal_info in *)
                  let subst, terms1, terms2 = unify_term_lists constants body hyp_info.tptp_body in
                  let subst, goal_info' = new_goal constants subst terms1 terms2 in
                  let goal = mk_goal goal_info' in
                     incr refine_count;
                     assert_new_goal level constants subst i goal (nextT goal_info'), i + 1
               with
                  RefineError _ ->
                     find_hyp (i + 1)
                | exn ->
                     eprintf "Tptp_prove.exception: %s%t" (Printexc.to_string exn) eflush;
                     raise exn
         in
         let rec matchT i p =
            let tac, next = find_hyp i in
               (tac orelseT matchT next) p
         in
            matchT first_hyp p

let proveT bound p =
   eprintf "Tptp_prove.proveT: %d%t" bound eflush;
   let { sequent_goals = goals;
         sequent_hyps = hyps
       } = Sequent.explode_sequent p
   in
   let info = dest_hyps bound hyps in
   let info =
      { tptp_goal_cache = TptpCache.create info.tptp_constants;
        tptp_goal = dest_goal (SeqGoal.get goals 0);
        tptp_level = 0;
        tptp_info = info
      }
   in
      prove_auxT info p

(*
 * This tactic is just for performance testing.
 *)
let dupT = duplicate

let rec loopTestT i p =
   if i = 0 then
      proveT 100 p
   else
      begin
(*
         eprintf "Marshaling%t" eflush;
         Marshal.to_string proveT [Marshal.Closures];
         eprintf "Marshaled%t" eflush;
 *)
         (dupT thenLT [loopTestT (pred i); proveT 100]) p
      end

let testT p =
   refine_count := 0;
   fail_count := 0;
   let finalize () =
      eprintf "Refine count: %d Fail count: %d%t" !refine_count !fail_count eflush
   in
      (finalT finalize thenT timingT (loopTestT 200)) p

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
