(*
 * This is the proof procedure for TPTP.
 * The following procedure is not so efficient, but
 * we are mainly using it for performance analysis.
 *)

include Tptp

open Printf
open Nl_debug

open Refiner.Refiner
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermShape
open Refiner.Refiner.RefineError

open Tacticals

open Base_dtactic

open Itt_equal
open Itt_struct
open Itt_atom
open Itt_logic
open Itt_rfun

open Tptp

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

(*
 * Tabbing for printing.
 *)
let tab out i =
   for j = 0 to i do
      output_char out ' '
   done

(************************************************************************
 * TERM SET                                                             *
 ************************************************************************)

(*
 * This is a version of alpha equality on clauses
 * the returns a more more refined comparison.
 *)
let rec compare_terms bvars1 bvars2 term1 term2 =
   if is_var_term term1 then
      if is_var_term term2 then
         let v1 = dest_var term1 in
         let v2 = dest_var term2 in
            compare_vars bvars1 bvars2 v1 v2
      else
         -1
   else if is_var_term term2 then
      1
   else
      let shape1 = shape_of_term term1 in
      let shape2 = shape_of_term term2 in
         match compare shape1 shape2 with
            0 ->
               compare_term_lists bvars1 bvars2 (subterms_of_term term1) (subterms_of_term term2)
          | ord ->
               ord

and compare_term_lists bvars1 bvars2 terms1 terms2 =
   match terms1, terms2 with
      term1 :: terms1, term2 :: terms2 ->
         let ord = compare_terms bvars1 bvars2 term1 term2 in
            if ord = 0 then
               compare_term_lists bvars1 bvars2 terms1 terms2
            else
               ord
    | [], [] ->
         0
    | [], _ ->
         -1
    | _, [] ->
         1

and compare_vars bvars1 bvars2 v1 v2 =
   match bvars1, bvars2 with
      bvar1 :: bvars1, bvar2 :: bvars2 ->
         if v1 = bvar1 then
            if v2 = bvar2 then
               0
            else
               -1
         else if v2 = bvar2 then
            1
         else
            compare_vars bvars1 bvars2 v1 v2
    | _ ->
         compare v1 v2

(*
 * Splay set of terms.
 *)
module TermOrd =
struct
   type t = string list * term list

   let compare (bvars1, terms1) (bvars2, terms2) =
      match List.length bvars1 - List.length bvars2 with
         0 ->
            begin
               match List.length terms1 - List.length terms2 with
                  0 ->
                     compare_term_lists bvars1 bvars2 terms1 terms2
                | ord ->
                     ord
            end
       | ord ->
            ord
end

module TermSet = Splay_set.Make (TermOrd)

(************************************************************************
 * UNIFICATION                                                          *
 ************************************************************************)

(*
 * Unify two terms.
 *)
let unify_exn = RefineError ("unify", StringError "terms do not unify")

(*
 * Unify the term with as many terms in the list
 * as possible.  Return the unifier, and the
 * list of terms that did not match.
 *)
let rec unify_term_list foundp subst constants term1 = function
   term2 :: terms2 ->
      begin
         try
            let subst = unify subst constants term1 term2 in
               unify_term_list true subst constants term1 terms2
         with
            RefineError _ ->
               let subst, terms2 = unify_term_list foundp subst constants term1 terms2 in
                  subst, term2 :: terms2
      end
 | [] ->
      if foundp then
         subst, []
      else
         raise unify_exn

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
               let subst, terms2 = unify_term_list false [] constants term1 terms2 in
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
         raise unify_exn

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Spread the clause.
 *)
let dest_hyp t =
   let vars, body = dest_all t in
      vars, dest_or body

let dest_hyps hyps j =
   let len = SeqHyp.length hyps in
   let hyps' = Array.create len ([], []) in
      for i = j to len - 1 do
         match SeqHyp.get hyps i with
            Hypothesis (_, hyp) ->
               hyps'.(i) <- dest_hyp hyp
          | Context _ ->
               ()
      done;
      hyps'

let dest_goal t =
   let vars, body = dest_exists t in
      vars, dest_and body

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
                  first_clause_aux (i + 1) len (v :: constants) hyps
               else
                  i, constants
       | Context _ ->
            first_clause_aux (i + 1) len constants hyps

let first_clause hyps =
   first_clause_aux 0 (SeqHyp.length hyps) [] hyps

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
let rec new_vars varcount l = function
   _ :: vars ->
      let v = "Y" ^ string_of_int !varcount in
         incr varcount;
         new_vars varcount (v :: l) vars
 | [] ->
      l

(*
 * Remove the duplicates after the substitution.
 *)
let rec remove_term term = function
   term' :: terms ->
      if alpha_equal term term' then
         remove_term term terms
      else
         term' :: remove_term term terms
 | [] ->
      []

let rec remove_duplicates = function
   term :: terms ->
      term :: remove_duplicates (remove_term term terms)
 | [] ->
      []

(*
 * Build the new goal after a unification.
 *)
let mk_new_goal varcount subst constants terms1 terms2 =
   let vars, terms = List.split subst in
   let terms2 = List.map negate_term terms2 in
   let terms = List.map (fun t -> TermSubst.subst t terms vars) (terms1 @ terms2) in
   let body =
      if terms = [] then
         true_term
      else
         mk_and_term (remove_duplicates terms)
   in
   let vars = List_util.subtract (free_vars body) constants in
   let vars' = new_vars varcount [] vars in
   let body = TermSubst.subst body (List.map mk_var_term vars') vars in
      mk_exists_term vars' body

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
         let v = get_apply_var t in
         let _ =
            if !debug_tptp then
               eprintf "Tptp_prove.prove_wf: atomic %s%t" v eflush
         in
         let i = Sequent.get_decl_number p v in
            (atomicT i thenT prove_wf) p
      else if is_type_term goal then
         let t = dest_type_term goal in
         let v = get_apply_var t in
         let _ =
            if !debug_tptp then
               eprintf "Tptp_prove.prove_wf: type %s%t" v eflush
         in
         let i = Sequent.get_decl_number p v in
            (typeT i thenT prove_wf) p
      else
         raise (RefineError ("prove_wf", StringTermError ("goal not recognized", goal)))

(*
 * Try the clause with the negation of the current clause.
 *)
let rec neg_trivial i j p =
   if !debug_tptp then
      eprintf "Tptp_prove.neg_trivial: %d %d%t" i j eflush;
   if j = i then
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
   if j = i then
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
   let _, hyp = Sequent.nth_hyp p i in
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
   let _, hyp = Sequent.nth_hyp p i in
      if is_or_term hyp then
         (dT i thenLT [goal_or_trivial i;
                       decompose_clause i]) p
      else
         goal_or_trivial i p

(*
 * Instantiate the hyp with the substitution,
 *)
let rec instantiate_hyp subst i p =
   if !debug_tptp then
      eprintf "Tptp_prove.instantiate_hyp%t" eflush;
   let _, hyp = Sequent.nth_hyp p i in
      if is_all_term hyp then
         let v = var_of_all hyp in
         let t = List.assoc v subst in
            (withT t (dT i)
             thenLT [prove_wf;
                     instantiate_hyp subst (Sequent.hyp_count p + 1)]) p
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
let rec instantiate_goal subst i n p =
   if !debug_tptp then
      eprintf "Tptp_prove.instantiate_goal%t" eflush;
   let goal = Sequent.concl p in
      if is_exists_term goal then
         let v = var_of_exists goal in
         let t = List.assoc v subst in
            (withT t (dT 0)
             thenLT [prove_wf;
                     instantiate_goal subst i n]) p
      else if is_and_term goal then
         (dT 0 thenT instantiate_goal subst i n) p
      else
         (trivial_goal (Sequent.hyp_count p) n orelseT instantiate_hyp subst i) p

(*
 * Decompose the existential that has just been asserted.
 * Save the new vars that are created.
 *)
let rec decompose_exists arg p =
   if !debug_tptp then
      eprintf "Tptp_prove.decompose_exists%t" eflush;
   let i = Sequent.hyp_count p in
   let _, hyp = Sequent.nth_hyp p i in
      if is_exists_term hyp then
         (dT i thenT decompose_exists arg) p
      else if is_and_term hyp then
         (dT i thenT decompose_exists arg) p
      else
         let subst, i, n = arg in
            instantiate_goal subst i n p

(*
 * Assert and decompose the new goal.
 *)
let assert_new_goal level subst hyp_index goal tac p =
   if !debug_tptp_prove then
      eprintf "%aresolveT %d -> %a%t" tab level hyp_index debug_print goal eflush;
   (assertT goal
    thenLT [tac;
            decompose_exists (subst, hyp_index, Sequent.hyp_count p)]) p

(*
 * Main tactic to unify on a hyp.
 *)
let resolveT i p =
   let varcount = ref 0 in
   let _, hyp = Sequent.nth_hyp p i in
   let hvars, terms2 = dest_hyp hyp in
   let gvars, terms1 = dest_goal (Sequent.concl p) in
   let j, constants = first_clause (Sequent.explode_sequent p).sequent_hyps in
   let subst, terms1, terms2 = unify_term_lists constants terms1 terms2 in
   let goal = mk_new_goal varcount subst constants terms1 terms2 in
      assert_new_goal 0 subst i goal idT p

(************************************************************************
 * SEARCH                                                               *
 ************************************************************************)

(*
 * We maintain a list of
 *)
type t =
   { tptp_set : TermSet.t;
     tptp_level : int;
     tptp_first_hyp : int;
     tptp_constants : string list;
     tptp_hyps : (string list * term list) array
   }

let varcount = ref 0

(*
 * Failure cache.
 *)
let fail_cache = ref TermSet.empty

let add_failure vars terms =
   if not (TermSet.mem !fail_cache (vars, terms)) then
      fail_cache := TermSet.add (vars, terms) !fail_cache

let check_failure vars terms =
   if TermSet.mem !fail_cache (vars, terms) then
      raise (RefineError ("check_failure", StringError "goal previously failed"))

(*
 * Cycle detection.
 *)
let check_cycle set vars terms =
   if TermSet.mem set (vars, terms) then
      raise (RefineError ("check_cycle", StringError "repeated goal"))

(*
 * Proof procedure uses failure and cycle detection.
 *)
let failT gvars terms1 p =
   add_failure gvars terms1;
   raise (RefineError ("findResolventT", StringError "no resolvent found"))

let rec prove_auxT
    { tptp_set = set;
      tptp_level = level;
      tptp_constants = constants;
      tptp_first_hyp = first_hyp;
      tptp_hyps = hyps
    } p =
   let goal = Sequent.concl p in
      if !debug_tptp then
         eprintf "proveT: %a%t" debug_print goal eflush;
      if alpha_equal goal true_term then
         dT 0 p
      else
         let gvars, terms1 = dest_goal (Sequent.concl p) in
            check_cycle set gvars terms1;
            check_failure gvars terms1;
            let nextT =
               prove_auxT (**)
                  { tptp_set = TermSet.add (gvars, terms1) set;
                    tptp_level = level + 1;
                    tptp_constants = constants;
                    tptp_first_hyp = first_hyp;
                    tptp_hyps = hyps
                  }
            in
            let count = Sequent.hyp_count p in
            let rec onSomeHypT l i =
               if i = count then
                  List.rev (failT gvars terms1 :: l)
               else
                  let l =
                     try
                        let hvars, terms2 = hyps.(i - 1) in
                        let subst, terms1, terms2 = unify_term_lists constants terms1 terms2 in
                        let goal = mk_new_goal varcount subst constants terms1 terms2 in
                           (assert_new_goal level subst i goal nextT) :: l
                     with
                        RefineError _ ->
                           l
                  in
                     onSomeHypT l (i + 1)
            in
               firstT (onSomeHypT [] first_hyp) p

let proveT p =
   let hyps = (Sequent.explode_sequent p).sequent_hyps in
   let j, constants = first_clause hyps in
   let hyps = dest_hyps hyps j in
   let info =
      { tptp_set = TermSet.empty;
        tptp_level = 0;
        tptp_first_hyp = j;
        tptp_constants = constants;
        tptp_hyps = hyps
      }
   in
      prove_auxT info p

(*
 * This tactic is just for performance testing.
 *)
let loopTestT p =
   for i = 0 to 20 do
      Tactic_type.refine proveT p
   done

let testT p =
   Utils.time_it loopTestT p;
   idT p

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
