(*
 * The refiner deals with proofs and functions on them.
 * We have the following objects in a refiner:
 *    + validation: a validation is a function on proofs
 *       for instance:
 *           f: (H, x:A, y:B, J[pair(x, y)] >> C[pair(x, y)]) -->
 *               (H, x:A, J[x] >> C[x])
 *        this declares "f" to be a validation, which is a function
 *        that takes a proof of the first sequent, and produces a
 *        proof of the second.  These validations can have
 *        arbitrary arity.
 *    + extract: an extract is a form of validation generated
 *          during proof refinement using tactics.
 *    + tactic: a tactic is a "reverse" application of a
 *      validation.  That is, given a validation f: A --> B,
 *      to produce a proof of B, all that is necessary is to
 *      produce a proof of A (modus ponens).
 *
 *    + rewrite: a rewrite can be reduced to an equivalence
 *      of terms in any context:
 *         f: A <--> B
 *      declares a rewrite that will convert an A to a B, or
 *      vice versa in any context.  This is the same as the
 *      validation:
 *         f: C:[A] <--> C:[B]
 *
 *    + cond_rewrite: conditional rewrite that requires
 *      a proof to be valid.  For instance,
 *         p: (x in A # B) --> (pair(x.1, x.2) <--> x)
 *      this rewrite can only be applied in a sequent
 *      calculus, and it means:
 *         p: (H >> x in A # B) --> (C:[pair(x.1, x.2)] <--> C:[x])
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

INCLUDE "refine_error.mlh"

open Printf
open Mp_debug

open Opname
open Term_sig
open Term_base_sig
open Term_man_sig
open Term_subst_sig
open Term_addr_sig
open Term_meta_sig
open Refine_error_sig
open Rewrite_sig
open Refine_sig

(*
 * Show the file loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Refine%t" eflush

let debug_refiner =
   create_debug (**)
      { debug_name = "refine";
        debug_description = "Display refinement operations";
        debug_value = false
      }

let debug_sentinal =
   create_debug (**)
      { debug_name = "sentinal";
        debug_description = "Display sentinal operations";
        debug_value = false
      }

module Refine (**)
   (TermType : TermSig)
   (Term : TermBaseSig
    with type term = TermType.term)
   (TermMan : TermManSig
    with type term = TermType.term)
   (TermSubst : TermSubstSig
    with type term = TermType.term)
   (TermAddr : TermAddrSig
    with type term = TermType.term)
   (TermMeta : TermMetaSig
    with type term = TermType.term)
   (Rewrite : RewriteSig
    with type term = TermType.term
    with type address = TermAddr.address)
   (RefineError : RefineErrorSig
    with type term = TermType.term
    with type address = TermAddr.address
    with type meta_term = TermMeta.meta_term) =
struct
   open TermType
   open Term
   open TermMan
   open TermSubst
   open TermAddr
   open TermMeta
   open Rewrite
   open RefineError

   type term = TermType.term
   type address = TermAddr.address
   type meta_term = TermMeta.meta_term

   (*
    * Refinements are on meta-sequents,
    * which are a restricted form of meta terms,
    * having only dependent functions format.
    *
    * Each hyp is labelled by its first argument.
    *)
   type msequent =
      { mseq_vars : string list;
        mseq_goal : term;
        mseq_hyps : term list
      }

   (*
    * A ML rewrite replaces a term with another,
    * no extract.
    *)
   type ml_rewrite =
      { ml_rewrite_rewrite :
           string array ->
           string list list ->
           term list ->
           term ->
           term ->
           term * term list * string array;
        ml_rewrite_extract : (string array * term list) -> term list -> term * term list
      }

   (*
    * A condition relaces an goal with a list of subgoals,
    * and it provides a function to compute the extract.
    *)
   type ml_rule =
      { ml_rule_rewrite :
           address array ->                     (* context addresses *)
           string array ->                      (* variable names *)
           msequent ->                          (* goal *)
           term list ->                         (* params *)
           msequent list * string array;        (* subgoals, new variable names *)
        ml_rule_extract : (string array * term list) -> term list -> term * term list
      }

   (************************************************************************
    * TYPES                                                                *
    ************************************************************************)

   (*
    * A proof has either been computed,
    * or the computation is delayed.
    *)
   type 'a proof =
      Extracted of 'a
    | Delayed of (unit -> 'a)

   (*
    * An extract summarizes a validation that is generated by a tactic.
    *
    * The extract type is a tree of terms.  The substitution is
    * delayed, since in most cases the extract term is never
    * computed.
    *
    * The refiner describes the rule that was applied, and
    * in most cases we also list the params to the rule that
    * was applied so that the validation can be called if
    * necessary.  The head rule of the refiner is the applied
    * rule.
    *)
   type extract =
      { ext_goal : msequent;
        ext_just : ext_just;
        ext_subgoals : msequent list
      }

   and ext_just =
      SingleJust of single_just
    | RewriteJust of rewrite_just
    | PairJust of ext_just * ext_just
    | ComposeJust of ext_just * ext_just list
    | NthHypJust of int

   and single_just =
      { (* Parameters to the rule and the rule itself *)
         ext_names : string array;
         ext_params : term list;
         ext_refiner : opname
      }

   and rewrite_just =
      RewriteCut of term
    | RewriteHere of opname
    | RewriteAddr of address * rewrite_just
    | RewriteHigher of rewrite_just list
    | RewritePair of rewrite_just * rewrite_just

   (*
    * A refiner contains the following items:
    *    + theorems: terms that are true in a sequent calculus
    *    + rules: implications on proofs
    *    + rewrite: term equivalences in any context
    *    + ml versions of the above
    *
    * refiners can be combined using PairRefiner.
    *)
   and refiner =
      NullRefiner

    | AxiomRefiner of axiom_refiner
    | PrimAxiomRefiner of prim_axiom_refiner

    | RuleRefiner of rule_refiner
    | PrimRuleRefiner of prim_rule_refiner
    | MLRuleRefiner of ml_rule_refiner

    | RewriteRefiner of rewrite_refiner
    | PrimRewriteRefiner of prim_rewrite_refiner

    | CondRewriteRefiner of cond_rewrite_refiner
    | PrimCondRewriteRefiner of prim_cond_rewrite_refiner
    | MLRewriteRefiner of ml_rewrite_refiner

    | PairRefiner of refiner * refiner
    | ListRefiner of refiner list
    | LabelRefiner of string * refiner

   and axiom_refiner =
      { axiom_name : opname;
        axiom_term : term;
        axiom_refiner : refiner
      }
   and prim_axiom_refiner =
      { mutable pax_proof : term proof;
        pax_axiom : axiom_refiner;
        pax_refiner : refiner
      }

   and rule_refiner =
      { rule_name : opname;
        rule_count : int;
        rule_rule : msequent;
        rule_refiner : refiner
      }
   and prim_rule_refiner =
      { mutable prule_proof : (string array -> term list -> term list -> term) proof;
        prule_rule : rule_refiner;
        prule_refiner : refiner
      }
   and ml_rule_refiner =
      { ml_rule_name : opname;
        ml_rule_info : ml_rule;
        ml_rule_refiner : refiner
      }

   and rewrite_refiner =
      { rw_name : opname;
        rw_rewrite : term * term;
        rw_refiner : refiner
      }
   and prim_rewrite_refiner =
      { mutable prw_proof : unit proof;
        prw_rewrite : rewrite_refiner;
        prw_refiner : refiner
      }

   and cond_rewrite_refiner =
      { crw_name : opname;
        crw_count : int;
        crw_rewrite : term list * term * term;
        crw_refiner : refiner
      }
   and prim_cond_rewrite_refiner =
      { mutable pcrw_proof : unit proof;
        pcrw_rewrite : cond_rewrite_refiner;
        pcrw_refiner : refiner
      }
   and ml_rewrite_refiner =
      { ml_rw_name : opname;
        ml_rw_info : ml_rewrite;
        ml_rw_refiner : refiner
      }

   (*
    * A Build has a reference to a refiner,
    * and the opname of this module.
    *)
   type build =
      { build_opname : opname;
        mutable build_refiner : refiner
      }

   (*
    * A hashtable is constructed for looking up justifications.
    *)
   type hash =
      { hash_rewrite : (opname, prim_rewrite_refiner) Hashtbl.t;
        hash_cond_rewrite : (opname, prim_cond_rewrite_refiner) Hashtbl.t;
        hash_axiom : (opname, prim_axiom_refiner) Hashtbl.t;
        hash_rule : (opname, prim_rule_refiner) Hashtbl.t;
        hash_refiner : (opname, refiner) Hashtbl.t
      }

   type find =
      { find_rewrite : opname -> prim_rewrite_refiner;
        find_cond_rewrite : opname -> prim_cond_rewrite_refiner;
        find_axiom : opname -> prim_axiom_refiner;
        find_rule : opname -> prim_rule_refiner;
        find_refiner : opname -> refiner
      }

   type check =
      { check_rewrite : rewrite_refiner -> prim_rewrite_refiner;
        check_cond_rewrite : cond_rewrite_refiner -> prim_cond_rewrite_refiner;
        check_axiom : axiom_refiner -> prim_axiom_refiner;
        check_rule : rule_refiner -> prim_rule_refiner
      }

   (*
    * This has a similar function.
    * It checks to see if justifications are justifiable.
    *)
   type sentinal =
      { sent_rewrite : rewrite_refiner -> unit;
        sent_cond_rewrite : cond_rewrite_refiner -> unit;
        sent_ml_rewrite : ml_rewrite_refiner -> unit;
        sent_axiom : axiom_refiner -> unit;
        sent_rule : rule_refiner -> unit;
        sent_ml_rule : ml_rule_refiner -> unit
      }

   (*
    * The tactic type is the basic refinement type, and every
    * element of tactic always produces "correct" refinements
    * by construction.  In other words, only primitive rules can
    * be directly injected into the tactic type, and all else is
    * by composition.
    *)
   type tactic = sentinal -> msequent -> msequent list * ext_just

   (*
    * A rewrite replaces a term with another term.
    *)
   type rw = sentinal -> term -> term * rewrite_just

   (*
    * A conditional rewrite takes a goal, then applies the rewrite
    * and generates subgoals.  The first argument is the sequent
    * the rewrite is being applied to, and the second is the
    * particular subterm to be rewritted.
    *)
   type cond_rewrite = sentinal -> string list list -> term -> term -> term * term list * ext_just

   (*
    * These are the forms created at compile time.
    *)
   type prim_tactic = address array * string array -> term list -> tactic
   type prim_rewrite = rw
   type prim_cond_rewrite = string array * term list -> cond_rewrite

   (*
    * For destruction.
    *)
   type refiner_item =
      RIAxiom of ri_axiom
    | RIRule of ri_rule
    | RIPrimTheorem of ri_prim_theorem
    | RIMLRule of ri_ml_rule

    | RIRewrite of ri_rewrite
    | RICondRewrite of ri_cond_rewrite
    | RIPrimRewrite of ri_prim_rewrite
    | RIMLRewrite of ri_ml_rewrite

    | RIParent of refiner
    | RILabel of string

   and ri_axiom =
      { ri_axiom_name : opname;
        ri_axiom_term : term
      }
   and ri_rule =
      { ri_rule_name : opname;
        ri_rule_rule : msequent
      }
   and ri_ml_rule =
      { ri_ml_rule_name : opname }
   and ri_prim_theorem =
      { ri_pthm_axiom : refiner }

   and ri_rewrite =
      { ri_rw_name : opname;
        ri_rw_redex : term;
        ri_rw_contractum : term
      }
   and ri_cond_rewrite =
      { ri_crw_name : opname;
        ri_crw_conds : term list;
        ri_crw_redex : term;
        ri_crw_contractum : term
      }
   and ri_prim_rewrite =
      { ri_prw_rewrite : refiner }
   and ri_ml_rewrite =
      { ri_ml_rw_name : opname }

   (************************************************************************
    * SEQUENT OPERATIONS                                                   *
    ************************************************************************)

   (*
    * Free var calculations when the sequent is constructed.
    *)
   let mk_msequent goal subgoals =
      { mseq_goal = goal;
        mseq_hyps = subgoals;
        mseq_vars = free_vars_terms (goal :: subgoals)
      }

   let dest_msequent mseq =
      mseq.mseq_goal, mseq.mseq_hyps

   let dest_msequent_vars mseq =
      mseq.mseq_vars, mseq.mseq_goal, mseq.mseq_hyps

    (*
     * Check that all the hyps in the list are equal.
     *)
   let equal_hyps hyps t =
      let check hyps' =
         List.for_all2 alpha_equal hyps' hyps
      in
         List.for_all check t

   (*
    * Compare two sequents for alpha eqivalence.
    *)
   let msequent_alpha_equal seq1 seq2 =
      if seq1 == seq2 then
         (* This is the common case *)
         true
      else
         let { mseq_goal = goal1; mseq_hyps = hyps1 } = seq1 in
         let { mseq_goal = goal2; mseq_hyps = hyps2 } = seq2 in
         let rec compare = function
            hyp1::hyps1, hyp2::hyps2 ->
               alpha_equal hyp1 hyp2 & compare (hyps1, hyps2)
          | [], [] ->
               true
          | _ ->
               false
         in
            alpha_equal goal1 goal2 & compare (hyps1, hyps2)

   (*
    * Split the goals from the hyps.
    *)
   let rec split_msequent_list = function
      { mseq_goal = goal; mseq_hyps = hyps }::t ->
         let goals, hypsl = split_msequent_list t in
            goal :: goals, hyps :: hypsl
    | [] ->
         [], []

   (************************************************************************
    * TACTICS                                                              *
    ************************************************************************)

   (*
    * Refinement is just application.
    * The application is doubled: the first argument is
    * for type tactic, and the second is for type safe_tactic.
    *)
   let refine sent (tac : tactic) (seq : msequent) =
      let subgoals, just = tac sent seq in
         subgoals, { ext_goal = seq; ext_just = just; ext_subgoals = subgoals }

   (*
    * NTH_HYP
    * The base tactic proves by assumption.
    *)
   let nth_hyp i sent seq =
      let { mseq_goal = goal; mseq_hyps = hyps } = seq in
         try
            if alpha_equal (List.nth hyps i) goal then
               [], NthHypJust i
            else
               REF_RAISE(RefineError ("nth_hyp", StringError "hyp mismatch"))
         with
            Failure "nth" ->
               REF_RAISE(RefineError ("nth_hyp", IntError i))

   (*
    * COMPOSE
    * Compose two extracts.
    * The subgoals of the first must match with the goals of the second.
    *)
   let compose ext extl =
      let { ext_goal = goal; ext_just = just; ext_subgoals = subgoals } = ext in
      let subgoals' = List.map (fun ext -> ext.ext_goal) extl in
      let _ =
         if not (List_util.for_all2 msequent_alpha_equal subgoals subgoals') then
            REF_RAISE(RefineError ("compose", StringError "goal mistmatch"))
      in
      let justl = List.map (fun ext -> ext.ext_just) extl in
      let just = ComposeJust (just, justl) in
      let subgoals'' = List_util.flat_map (fun ext -> ext.ext_subgoals) extl in
         { ext_goal = goal; ext_just = just; ext_subgoals = subgoals }

   (************************************************************************
    * REGULAR REWRITES                                                     *
    ************************************************************************)

   (*
    * Convert a rewrite to a tactic.
    *)
   let rwtactic (rw : rw) sent (seq : msequent) =
      let { mseq_vars = vars; mseq_goal = goal; mseq_hyps = hyps } = seq in
      let goal, just = rw sent goal in
         [{ mseq_vars = vars; mseq_goal = goal; mseq_hyps = hyps }], RewriteJust just

   (*
    * Apply a rewrite at an address.
    *)
   let rwaddr addr rw sent t =
      let t, just = apply_fun_arg_at_addr (rw sent) addr t in
         t, RewriteAddr (addr, just)

   (*
    * Apply the rewrite to the outermost terms where it
    * does not fail.
    *)
   let rwhigher rw sent t =
      let t, justs = apply_fun_higher (rw sent) t in
         t, RewriteHigher justs

   (*
    * Composition is supplied for efficiency.
    *)
   let andthenrw rw1 rw2 sent t =
      let t', just =
         IFDEF VERBOSE_EXN THEN
            try rw1 sent t with
               RefineError (name, x) ->
                  raise (RefineError ("andthenrw", GoalError (name, x)))
         ELSE
            rw1 sent t
         ENDIF
      in
      let t'', just' =
         IFDEF VERBOSE_EXN THEN
            try rw2 sent t' with
               RefineError (name, x) ->
                  raise (RefineError ("andthenrw", SecondError (name, x)))
         ELSE
            rw2 sent t'
         ENDIF
      in
         t'', RewritePair (just, just')

   let orelserw rw1 rw2 sent t =
      IFDEF VERBOSE_EXN THEN
         try rw1 sent t with
            RefineError (name1, x) ->
               try rw2 sent t with
                  RefineError (name2, y) ->
                     raise (RefineError ("orelserw", PairError (name1, x, name2, y)))
      ELSE
         try rw1 sent t with
            _ ->
               rw2 sent t
      ENDIF

   (************************************************************************
    * CONDITIONAL REWRITES                                                 *
    ************************************************************************)

   (*
    * Inject a regular rewrite as a conditional rewrite.
    *)
   let mk_cond_rewrite rw sent _ _ t =
      let arg, just = rw sent t in
         arg, [], RewriteJust just

   (*
    * Cut rule in a sequent calculus.
    *)
   let cutrw t' sent _ seq t =
      let rw = mk_xrewrite_term t' t in
      let seq = replace_goal seq rw in
         t', [seq], RewriteJust (RewriteCut t')

   (*
    * Apply the rewrite to an addressed term.
    *)
   let crwaddr addr crw sent bvars seq t =
      LETMACRO BODY =
         let t, (subgoals, just) =
            let f sent bvars t =
               let t, subgoals, just = crw sent bvars seq t in
                  t, (subgoals, just)
            in
               apply_var_fun_arg_at_addr (f sent) addr bvars t
         in
            t, subgoals, just
      IN
      IFDEF VERBOSE_EXN THEN
         try BODY
         with
            RefineError (name, x) ->
               raise (RefineError ("crwaddr", RewriteAddressError (addr, name, x)))
      ELSE
         BODY
      ENDIF

   (*
    * Apply the rewrite at the outermost terms where it does not fail.
    *)
   let crwhigher crw sent bvars seq t =
      let t, args =
         let f sent bvars t =
            let t, subgoals, just = crw sent bvars seq t in
               t, (subgoals, just)
         in
            apply_var_fun_higher (f sent) bvars t
      in
      let rec flatten = function
         [subgoals, just] ->
            subgoals, just
       | (subgoals, just) :: tl ->
            let subgoals', just' = flatten tl in
               subgoals @ subgoals', PairJust (just, just')
       | [] ->
            raise (RefineError ("crwhigher", StringError "operation made no progress"))
      in
      let subgoals, just = flatten args in
         t, subgoals, just

   (*
    * Apply a conditional rewrite.
    *)
   let crwtactic (rw : cond_rewrite) (sent : sentinal) (seq : msequent) =
      let { mseq_vars = vars; mseq_goal = goal; mseq_hyps = hyps } = seq in
      let t', subgoals, just = rw sent [vars] goal goal in
      let mk_subgoal subgoal =
         { mseq_vars = vars; mseq_goal = subgoal; mseq_hyps = hyps }
      in
      let subgoals' = List.map mk_subgoal (t' :: subgoals) in
         subgoals', just

   (*
    * Composition is supplied for efficiency.
    *)
   let candthenrw crw1 crw2 sent bvars seq t =
      let t', subgoals, just =
         IFDEF VERBOSE_EXN THEN
            try crw1 sent bvars seq t with
               RefineError (name, x) ->
                  raise (RefineError ("candthenrw", GoalError (name, x)))
         ELSE
            crw1 sent bvars seq t
         ENDIF
      in
      let t'', subgoals', just' =
         IFDEF VERBOSE_EXN THEN
            try crw2 sent bvars seq t' with
               RefineError (name, x) ->
                  raise (RefineError ("candthenrw", SecondError (name, x)))
         ELSE
            crw2 sent bvars seq t'
         ENDIF
      in
         t'', subgoals @ subgoals', PairJust (just, just')

   let corelserw crw1 crw2 sent bvars seq t =
      IFDEF VERBOSE_EXN THEN
         try crw1 sent bvars seq t with
            RefineError (name1, x) ->
               try crw2 sent bvars seq t with
                  RefineError (name2, y) ->
                     raise (RefineError ("corelserw", PairError (name1, x, name2, y)))
      ELSE
         try crw1 sent bvars seq t with
            _ ->
               crw2 sent bvars seq t
      ENDIF

   (************************************************************************
    * UTILITIES                                                            *
    ************************************************************************)

   (*
    * Empty refiner.
    *)
   let null_refiner name =
      { build_opname = mk_opname name nil_opname;
        build_refiner = NullRefiner
      }

   let refiner_of_build build =
      build.build_refiner

   (*
    * Combine the refiners into a single refiner.
    *)
   let join_refiner build ref1 =
      build.build_refiner <- PairRefiner (build.build_refiner, ref1)

   (*
    * Label a refiner with the name of the module.
    *)
   let label_refiner build name =
      let refiner = LabelRefiner (name, build.build_refiner) in
         build.build_refiner <- refiner;
         refiner

   (*
    * Search for an axiom by name.
    *)
   let find_refiner refiner name =
      let rec search refiners refiner =
         match refiner with
            NullRefiner ->
               refiners, None
          | AxiomRefiner { axiom_name = n; axiom_refiner = next } as r ->
               if n = name then
                  refiners, Some r
               else
                  search refiners next
          | PrimAxiomRefiner { pax_refiner = next } ->
               search refiners next

          | RuleRefiner { rule_name = n; rule_refiner = next } as r ->
               if n = name then
                  refiners, Some r
               else
                  search refiners next
          | PrimRuleRefiner { prule_refiner = next } ->
               search refiners next
          | MLRuleRefiner { ml_rule_refiner = next } ->
               search refiners next

          | RewriteRefiner { rw_name = n; rw_refiner = next } as r ->
               if n = name then
                  refiners, Some r
               else
                  search refiners next
          | PrimRewriteRefiner { prw_refiner = next } ->
               search refiners next

          | CondRewriteRefiner { crw_name = n; crw_refiner = next } as r ->
               if n = name then
                  refiners, Some r
               else
                  search refiners next
          | PrimCondRewriteRefiner { pcrw_refiner = next } ->
               search refiners next
          | MLRewriteRefiner { ml_rw_name = n; ml_rw_refiner = next } as r ->
               if n = name then
                  REF_RAISE(RefineError (string_of_opname n, StringError "ML rewrites can't be justified"))
               else
                  search refiners next

          | LabelRefiner (_, next) as r ->
               if List.memq r refiners then
                  refiners, None
               else
                  search (r :: refiners) next
          | PairRefiner (next1, next2) ->
               begin
                  match search refiners next1 with
                     refiners, None ->
                        search refiners next2
                   | x ->
                        x
               end
          | ListRefiner refiners' ->
               let rec search' refiners = function
                  refiner :: tl ->
                     begin
                        match search refiners refiner with
                           refiners, None ->
                              search' refiners tl
                         | x ->
                              x
                     end
                | [] ->
                     refiners, None
               in
                  search' refiners refiners'
      in
         match search [] refiner with
            _, Some v ->
               v
          | _ ->
               raise Not_found

   (************************************************************************
    * EXTRACTION                                                           *
    ************************************************************************)

   (*
    * When an term is calculated from an extract, we have to search
    * for the justifications in the current refiner.  We save them
    * in a hashtable by their names and their types.
    *)
   let hash_refiner refiner =
      let rewrites = Hashtbl.create 19 in
      let cond_rewrites = Hashtbl.create 19 in
      let axioms = Hashtbl.create 19 in
      let rules = Hashtbl.create 19 in
      let refiners = Hashtbl.create 19 in
      let maybe_add hash name info =
         try Hashtbl.find hash name; () with
            Not_found ->
               Hashtbl.add hash name info
      in
      let rec insert refiners' refiner =
         match refiner with
            PrimAxiomRefiner pax ->
               let { pax_axiom = { axiom_name = name }; pax_refiner = next } = pax in
                  maybe_add axioms name pax;
                  maybe_add refiners name refiner;
                  insert refiners' next
          | PrimRuleRefiner prule ->
               let { prule_rule = { rule_name = name }; prule_refiner = next } = prule in
                  maybe_add rules name prule;
                  maybe_add refiners name refiner;
                  insert refiners' next
          | PrimRewriteRefiner prw ->
               let { prw_rewrite = { rw_name = name }; prw_refiner = next  } = prw in
                  maybe_add rewrites name prw;
                  maybe_add refiners name refiner;
                  insert refiners' next
          | PrimCondRewriteRefiner pcrw ->
               let { pcrw_rewrite = { crw_name = name }; pcrw_refiner = next  } = pcrw in
                  maybe_add cond_rewrites name pcrw;
                  maybe_add refiners name refiner;
                  insert refiners' next
          | AxiomRefiner { axiom_refiner = next } ->
               insert refiners' next
          | RuleRefiner { rule_refiner = next } ->
               insert refiners' next
          | RewriteRefiner { rw_refiner = next } ->
               insert refiners' next
          | CondRewriteRefiner { crw_refiner = next } ->
               insert refiners' next
          | MLRewriteRefiner { ml_rw_refiner = next } ->
               insert refiners' next
          | MLRuleRefiner { ml_rule_refiner = next } ->
               insert refiners' next
          | LabelRefiner (_, next) as r ->
               if List.memq r refiners' then
                  refiners'
               else
                  insert (r :: refiners') next
          | PairRefiner (next1, next2) ->
               insert (insert refiners' next1) next2
          | ListRefiner refiners'' ->
               List.fold_left insert refiners' refiners''
          | NullRefiner ->
               refiners'
      in
      let _ = insert [] refiner in
         { hash_axiom = axioms;
           hash_rule = rules;
           hash_rewrite = rewrites;
           hash_cond_rewrite = cond_rewrites;
           hash_refiner = refiners
         }

   (*
    * Lookup values in the hashtable, or print error messages.
    *)
   let find_of_hash { hash_axiom = axioms;
                      hash_rule = rules;
                      hash_rewrite = rewrites;
                      hash_cond_rewrite = cond_rewrites;
                      hash_refiner = refiners
       } =
      let find_axiom name =
         try Hashtbl.find axioms name with
            Not_found ->
               REF_RAISE(RefineError (string_of_opname name, StringError "axiom is not justified"))
      in
      let find_rule name =
         try Hashtbl.find rules name with
            Not_found ->
               REF_RAISE(RefineError (string_of_opname name, StringError "rule is not justified"))
      in
      let find_rewrite name =
         try Hashtbl.find rewrites name with
            Not_found ->
               REF_RAISE(RefineError (string_of_opname name, StringError "rewrite is not justified"))
      in
      let find_cond_rewrite name =
         try Hashtbl.find cond_rewrites name with
            Not_found ->
               REF_RAISE(RefineError (string_of_opname name, StringError "cond_rewrite is not justified"))
      in
      let find_refiner name =
         try Hashtbl.find refiners name with
            Not_found ->
               REF_RAISE(RefineError (string_of_opname name, StringError "refiner is not justified"))
      in
         { find_axiom = find_axiom;
           find_rule = find_rule;
           find_rewrite = find_rewrite;
           find_cond_rewrite = find_cond_rewrite;
           find_refiner = find_refiner
         }

   (*
    * Also sent the matching.
    *)
   let check_of_find { find_axiom = find_axiom;
                       find_rule = find_rule;
                       find_rewrite = find_rewrite;
                       find_cond_rewrite = find_cond_rewrite
       } =
      let check_axiom ax =
         let { axiom_name = name } = ax in
         let pax = find_axiom name in
            if pax.pax_axiom == ax then
               pax
            else
               REF_RAISE(RefineError (string_of_opname name, StringError "axiom proof does not match"))
      in
      let check_rule rule =
         let { rule_name = name } = rule in
         let prule = find_rule name in
            if prule.prule_rule == rule then
               prule
            else
               REF_RAISE(RefineError (string_of_opname name, StringError "rule proof does not match"))
      in
      let check_rewrite rw =
         let { rw_name = name } = rw in
         let prw = find_rewrite name in
            if prw.prw_rewrite == rw then
               prw
            else
               REF_RAISE(RefineError (string_of_opname name, StringError "rewrite proof does not match"))
      in
      let check_cond_rewrite crw =
         let { crw_name = name } = crw in
         let pcrw = find_cond_rewrite name in
            if pcrw.pcrw_rewrite == crw then
               pcrw
            else
               REF_RAISE(RefineError (string_of_opname name, StringError "cond_rewrite proof does not match"))
      in
         { check_axiom = check_axiom;
           check_rule = check_rule;
           check_rewrite = check_rewrite;
           check_cond_rewrite = check_cond_rewrite
         }

   (*
    * Get the extract term for an axiom.
    *)
   let axiom_proof pax =
      match pax.pax_proof with
         Extracted t ->
            t
       | Delayed f ->
            let t = f () in
               pax.pax_proof <- Extracted t;
               t

   let rule_proof prule =
      match prule.prule_proof with
         Extracted t ->
            t
       | Delayed f ->
            let t = f () in
               prule.prule_proof <- Extracted t;
               t

   let rewrite_proof prw =
      match prw.prw_proof with
         Extracted () ->
            ()
       | Delayed f ->
            prw.prw_proof <- Extracted (f ())

   let cond_rewrite_proof pcrw =
      match pcrw.pcrw_proof with
         Extracted () ->
            ()
       | Delayed f ->
            pcrw.pcrw_proof <- Extracted (f ())

   (*
    * Expand the extracts of the components.
    *)
   let check = function
      PrimAxiomRefiner pax ->
         let _ = axiom_proof pax in
            ()
    | PrimRuleRefiner prule ->
         let _ = rule_proof prule in
            ()
    | PrimRewriteRefiner prw ->
         rewrite_proof prw;
         ()
    | PrimCondRewriteRefiner pcrw ->
         cond_rewrite_proof pcrw;
         ()
    | _ ->
         ()

   (*
    * Check for a valid rewrite justification.
    *)
   let rec check_rewrite_just check = function
      RewriteHere op ->
         check op
    | RewriteAddr (_, just) ->
         check_rewrite_just check just
    | RewritePair (just1, just2) ->
         check_rewrite_just check just1;
         check_rewrite_just check just2
    | RewriteHigher justs ->
         List.iter (check_rewrite_just check) justs
    | RewriteCut _ ->
         ()

   (*
    * Get the term from an extract.
    * This will fail if some of the rules are not justified.
    *)
   let term_of_extract refiner { ext_just = just } (args : term list) =
      let find = find_of_hash (hash_refiner refiner) in
      let { find_refiner = find_refiner } = find in
      let { check_axiom = find_axiom;
            check_rule = find_rule;
            check_rewrite = find_rewrite;
            check_cond_rewrite = find_cond_rewrite
          } = check_of_find find
      in
      let split_first = function
         h::t ->
            h, t
       | [] ->
            raise (Failure "Refine.term_of_extract: extract list is empty")
      in
      let split_list i l =
         try List_util.split_list i l with
            Failure _ ->
               raise (Failure "Refine.term_of_extract: extract list too short")
      in
      let nth_tl i l =
         try List_util.nth_tl i l with
            Failure _ ->
               raise (Failure "Refine.term_of_extract: extract list too short")
      in
      let check_rewrite just =
         check_rewrite_just (fun opname -> let _ = find_refiner opname in ()) just
      in
      let rec construct extracts = function
         SingleJust { ext_names = names; ext_params = params; ext_refiner = name } ->
            begin
               match find_refiner name with
                  AxiomRefiner ax ->
                     axiom_proof (find_axiom ax), extracts
                | RuleRefiner rule ->
                     let { rule_count = count } = rule in
                     let hd, tl = split_list count extracts in
                        rule_proof (find_rule rule) names params hd, tl
                | MLRuleRefiner { ml_rule_info = { ml_rule_extract = f } } ->
                     f (names, params) extracts
                | RewriteRefiner rw ->
                     let _ = find_rewrite rw in
                        split_first extracts
                | CondRewriteRefiner crw ->
                     let { crw_count = count } = crw in
                     let hd, tl = split_first extracts in
                     let _ = find_cond_rewrite crw in
                        hd, nth_tl count tl
                | MLRewriteRefiner { ml_rw_info = { ml_rewrite_extract = f } } ->
                     f (names, params) extracts
                | _ ->
                     raise (Failure "Refine.term_of_extract: refine error")
            end
       | RewriteJust just ->
            check_rewrite just;
            split_first extracts
       | PairJust (just1, just2) ->
            let extract, extracts = construct extracts just2 in
               construct (extract :: extracts) just1
       | ComposeJust (just, justl) ->
            let rec collect extracts = function
               just :: justl ->
                  let extract, extracts = construct extracts just in
                     extract :: collect extracts justl
             | [] ->
                  extracts
            in
               construct (collect extracts justl) just
       | NthHypJust i ->
            List.nth args i, extracts
      in
         fst (construct [] just)

   (*
    * An empty sentinal for trying refinements.
    *)
   let any_sentinal =
      let null _ =
         ()
      in
         { sent_rewrite = null;
           sent_cond_rewrite = null;
           sent_ml_rewrite = null;
           sent_axiom = null;
           sent_rule = null;
           sent_ml_rule = null
         }

   (*
    * The sentinal uses a hashtable to lookup valid inferences.
    *)
   let sentinal_of_refiner refiner =
      let rewrites = Hashtbl.create 19 in
      let cond_rewrites = Hashtbl.create 19 in
      let ml_rewrites = Hashtbl.create 19 in
      let axioms = Hashtbl.create 19 in
      let rules = Hashtbl.create 19 in
      let ml_rules = Hashtbl.create 19 in
      let rec insert refiners = function
         PrimAxiomRefiner { pax_refiner = next } ->
            insert refiners next
       | PrimRuleRefiner { prule_refiner = next } ->
            insert refiners next
       | PrimRewriteRefiner { prw_refiner = next } ->
            insert refiners next
       | PrimCondRewriteRefiner { pcrw_refiner = next } ->
            insert refiners next
       | AxiomRefiner ax ->
            let { axiom_name = name; axiom_refiner = next } = ax in
               IFDEF VERBOSE_EXN THEN
                  if !debug_sentinal then
                     eprintf "sentinal_of_refiner: add axiom %s%t" (string_of_opname name) eflush
               ENDIF;
               Hashtbl.add axioms name ax;
               insert refiners next
       | RuleRefiner rule ->
            let { rule_name = name; rule_refiner = next } = rule in
               IFDEF VERBOSE_EXN THEN
                  if !debug_sentinal then
                     eprintf "sentinal_of_refiner: add rule %s%t" (string_of_opname name) eflush
               ENDIF;
               Hashtbl.add rules name rule;
               insert refiners next
       | RewriteRefiner rw ->
            let { rw_name = name; rw_refiner = next } = rw in
               IFDEF VERBOSE_EXN THEN
                  if !debug_sentinal then
                     eprintf "sentinal_of_refiner: add rewrite %s%t" (string_of_opname name) eflush
               ENDIF;
               Hashtbl.add rewrites name rw;
               insert refiners next
       | CondRewriteRefiner crw ->
            let { crw_name = name; crw_refiner = next } = crw in
               IFDEF VERBOSE_EXN THEN
                  if !debug_sentinal then
                     eprintf "sentinal_of_refiner: add cond_rewrite %s%t" (string_of_opname name) eflush
               ENDIF;
               Hashtbl.add cond_rewrites name crw;
               insert refiners next
       | MLRewriteRefiner mlrw ->
            let { ml_rw_name = name; ml_rw_refiner = next } = mlrw in
               IFDEF VERBOSE_EXN THEN
                  if !debug_sentinal then
                     eprintf "sentinal_of_refiner: add ML rewrite %s%t" (string_of_opname name) eflush
               ENDIF;
               Hashtbl.add ml_rewrites name mlrw;
               insert refiners next
       | MLRuleRefiner mlrule ->
            let { ml_rule_name = opname; ml_rule_refiner = next } = mlrule in
               IFDEF VERBOSE_EXN THEN
                  if !debug_sentinal then
                     eprintf "sentinal_of_refiner: add ML rule %s%t" (string_of_opname opname) eflush
               ENDIF;
               Hashtbl.add ml_rules opname mlrule;
               insert refiners next
       | LabelRefiner (_, next) as r ->
            if List.memq r refiners then
               refiners
            else
               insert (r :: refiners) next
       | PairRefiner (next1, next2) ->
            insert (insert refiners next1) next2
       | ListRefiner refiners' ->
            List.fold_left insert refiners refiners'
       | NullRefiner ->
            refiners
      in
      let _ = insert [] refiner in
      let check_sentinal table name v =
         if try Hashtbl.find table name == v with Not_found -> false then
            IFDEF VERBOSE_EXN THEN
               if !debug_sentinal then
                  eprintf "check_sentinal: found %s%t" (string_of_opname name) eflush
            ENDIF
         else
            begin
               eprintf "check_sentinal: failed %s%t" (string_of_opname name) eflush;
               REF_RAISE(RefineError
                            ("check_sentinal",
                             StringStringError ("axiom is not valid in this context", (string_of_opname name))))
            end
      in
      let check_axiom ax = check_sentinal axioms ax.axiom_name ax in
      let check_rule rule = check_sentinal rules rule.rule_name rule in
      let check_ml_rule ml_rule =
         let opname = ml_rule.ml_rule_name in
            if try Hashtbl.find ml_rules opname == ml_rule with Not_found -> false then
               IFDEF VERBOSE_EXN THEN
                  if !debug_sentinal then
                     eprintf "check_ml_rule: found rule %s%t" (string_of_opname opname) eflush
               ENDIF
            else
               begin
                  eprintf "check_ml_rule: sentinal failed: %s%t" (string_of_opname opname) eflush;
                  REF_RAISE(RefineError ("check_ml_rule",
                                         StringStringError ("ML rule is not valid in this context",
                                                            string_of_opname opname)))
               end
      in
      let check_rewrite rw = check_sentinal rewrites rw.rw_name rw in
      let check_cond_rewrite crw = check_sentinal cond_rewrites crw.crw_name crw in
      let check_ml_rewrite mlrw = check_sentinal ml_rewrites mlrw.ml_rw_name mlrw in
         { sent_rewrite = check_rewrite;
           sent_cond_rewrite = check_cond_rewrite;
           sent_ml_rewrite = check_ml_rewrite;
           sent_axiom = check_axiom;
           sent_rule = check_rule;
           sent_ml_rule = check_ml_rule
         }

   (************************************************************************
    * AXIOM                                                                *
    ************************************************************************)

   (*
    * An theorem is a special case of a rule, where to
    * arity is 1, and there are no addrs or params.
    * Still get a tactic by this name (the equivalent
    * of BackThruLemma `name`).
    *)
   let check_axiom term =
      match TermSubst.context_vars term with
         [] ->
            ()
       | l ->
            REF_RAISE(RefineError ("check_axiom", RewriteFreeContextVars l))

   let add_axiom build name term =
      IFDEF VERBOSE_EXN THEN
         if !debug_refiner then
            eprintf "Refiner.add_axiom: %s%t" name eflush
      ENDIF;
      let { build_opname = opname; build_refiner = refiner } = build in
      let opname = mk_opname name opname in
      let ref_axiom =
         { axiom_name = opname;
           axiom_term = term;
           axiom_refiner = refiner
         }
      in
      let refiner' = AxiomRefiner ref_axiom in
      let tac _ _ (sent : sentinal) { mseq_goal = goal } =
         if alpha_equal (nth_concl goal 0) term then
            begin
               sent.sent_axiom ref_axiom;
               [], SingleJust { ext_names = [||]; ext_params = []; ext_refiner = opname }
            end
         else
            REF_RAISE(RefineError ("refine_axiom", TermMatchError (goal, name)))
      in
         let _ = check_axiom term in
         refiner', (tac : prim_tactic)

   let add_prim_axiom build name term =
      IFDEF VERBOSE_EXN THEN
         if !debug_refiner then
            eprintf "Refiner.prim_axiom: %s%t" name eflush
      ENDIF;
      let { build_opname = opname; build_refiner = refiner } = build in
         match find_refiner refiner (mk_opname name opname) with
            AxiomRefiner ax ->
               PrimAxiomRefiner { pax_proof = Extracted term;
                                  pax_axiom = ax;
                                  pax_refiner = refiner
               }
          | _ ->
               REF_RAISE(RefineError (name, StringError "not an axiom"))

   let add_delayed_axiom build name extf =
      IFDEF VERBOSE_EXN THEN
         if !debug_refiner then
            eprintf "Refiner.delayed_axiom: %s%t" name eflush
      ENDIF;
      let { build_opname = opname; build_refiner = refiner } = build in
         match find_refiner refiner (mk_opname name opname) with
            AxiomRefiner ax ->
               let compute () =
                  let { axiom_term = goal } = ax in
                  let ext = extf () in
                  let { ext_goal = { mseq_goal = goal' }; ext_subgoals = subgoals } = ext in
                     if not (alpha_equal (nth_concl goal' 0) goal) or subgoals != [] then
                        REF_RAISE(RefineError (name, StringError "not justified"));
                     term_of_extract refiner ext []
               in
                  PrimAxiomRefiner { pax_proof = Delayed compute;
                                     pax_axiom = ax;
                                     pax_refiner = refiner
                  }
          | _ ->
               REF_RAISE(RefineError (name, StringError "not an axiom"))

   (************************************************************************
    * RULE                                                                 *
    ************************************************************************)

   (*
    * Create a rule from a meta-term.
    * We allow first-order rules (T -> ... -> T)
    * where each T must be a term, and the arity is arbitrary,
    * and there are no dependencies.
    *)
   let add_rule build name addrs names params mterm =
      IFDEF VERBOSE_EXN THEN
         if !debug_refiner then
            eprintf "Refiner.add_rule: %s%t" name eflush
      ENDIF;
      let { build_opname = opname; build_refiner = refiner } = build in
      let terms = unzip_mimplies mterm in
      let subgoals, goal = List_util.split_last terms in
      let seq = mk_msequent goal subgoals in
      let rw = Rewrite.term_rewrite (addrs, names) (goal :: params) subgoals in
      let opname = mk_opname name opname in
      let ref_rule =
         { rule_name = opname;
           rule_count = List.length subgoals;
           rule_rule = seq;
           rule_refiner = refiner
         }
      in
      let refiner' = RuleRefiner ref_rule in
      let tac (addrs, names) params sent mseq =
         let vars = mseq.mseq_vars in
         let subgoals, names' = apply_rewrite rw (addrs, names, [vars]) mseq.mseq_goal params in
         let make_subgoal subgoal =
            { mseq_vars = vars; mseq_goal = subgoal; mseq_hyps = mseq.mseq_hyps }
         in
         let just =
            SingleJust { ext_names = names';
                         ext_params = params;
                         ext_refiner = opname
            }
         in
            sent.sent_rule ref_rule;
            List.map make_subgoal subgoals, just
      in
         refiner', (tac : prim_tactic)

   let ar0_ar0_null = ([||], [||], [])
   let ar0_ar0 = ([||], [||])

   (*
    * Theorem for a previous theorem or rule.
    * We once again use the rewriter to compute the
    * extract.  The subextracts are shaped into a
    * term of the form:
    *    lambda(a. lambda(b. ... cons(arg1; cons(arg2; ... cons(argn, nil)))))
    *)
   let compute_rule_ext name vars params args result =
      (* Create redex term *)
      let l = Array.length vars in
      let create_redex vars args =
         let args' = mk_xlist_term args in
         let rec aux j =
            if j < l then
               mk_xlambda_term vars.(j) (aux (j + 1))
            else
               args'
         in
            aux 0
      in
      let rw = Rewrite.term_rewrite ar0_ar0 (create_redex vars args :: params) [result] in
      let compute_ext vars params args =
         match apply_rewrite rw ar0_ar0_null (create_redex vars args) params with
            [c], x when Array.length x = 0 ->
               c
          | _ ->
               raise (Failure "Refine.add_prim_theorem.compute_ext: faulty extract")
      in
         compute_ext

   let add_prim_rule build name vars params args result =
      IFDEF VERBOSE_EXN THEN
         if !debug_refiner then
            eprintf "Refiner.add_prim_theorem: %s%t" name eflush
      ENDIF;
      let { build_opname = opname; build_refiner = refiner } = build in
         match find_refiner refiner (mk_opname name opname) with
            RuleRefiner rule ->
               let compute_ext = compute_rule_ext name vars params args result in
                  PrimRuleRefiner { prule_proof = Extracted compute_ext;
                                    prule_rule = rule;
                                    prule_refiner = refiner
                  }
          | _ ->
               REF_RAISE(RefineError (name, StringError "not a rule"))

   let add_delayed_rule build name vars params args ext =
      IFDEF VERBOSE_EXN THEN
         if !debug_refiner then
            eprintf "Refiner.delayed_rule: %s%t" name eflush
      ENDIF;
      let { build_opname = opname; build_refiner = refiner } = build in
         match find_refiner refiner (mk_opname name opname) with
            RuleRefiner rule ->
               let compute_ext () =
                  let ext = ext () in
                  let { rule_rule = goal } = rule in
                  let { ext_goal = goal'; ext_subgoals = subgoals } = ext in
                  let _ =
                     if not (msequent_alpha_equal goal' goal) or subgoals <> [] then
                        REF_RAISE(RefineError (name, StringError "extract does not match"))
                  in
                  let t = term_of_extract refiner ext args in
                     compute_rule_ext name vars params args t
               in
                  PrimRuleRefiner { prule_proof = Delayed compute_ext;
                                    prule_rule = rule;
                                    prule_refiner = refiner
                  }
          | _ ->
               REF_RAISE(RefineError (name, StringError "not a rule"))

   (*
    * An ML rule
    *)
   let add_ml_rule build name info =
      IFDEF VERBOSE_EXN THEN
         if !debug_refiner then
            eprintf "Refiner.add_ml_rule: %s%t" name eflush
      ENDIF;
      let { ml_rule_rewrite = rw } = info in
      let { build_opname = opname; build_refiner = refiner } = build in
      let opname = mk_opname name opname in
      let ref_rule =
         { ml_rule_name = opname;
           ml_rule_info = info;
           ml_rule_refiner = refiner
         }
      in
      let tac (addrs, names) params sent mseq =
         let subgoals, names = rw addrs names mseq params in
         let just =
            SingleJust { ext_names = names;
                         ext_params = params;
                         ext_refiner = opname
            }
         in
            sent.sent_ml_rule ref_rule;
            subgoals, just
      in
         MLRuleRefiner ref_rule, (tac : prim_tactic)

   (*
    * Just do the checking.
    *)
   let check_rule name addrs names params mterm =
      let terms = unzip_mimplies mterm in
      let subgoals, goal = List_util.split_last terms in
      let _ = Rewrite.term_rewrite (addrs, names) (goal::params) subgoals in
         ()

   (************************************************************************
    * REWRITE                                                              *
    ************************************************************************)

   (*
    * See if the rewrite will compile.
    *)
   let check_rewrite name vars params subgoals redex contractum =
      ignore(Rewrite.term_rewrite ([||], vars) (redex::params) [contractum])

   (*
    * Create a simple rewrite from a meta-term.
    * The rewrite must be a MetaIff.
    *)
   let add_rewrite build name redex contractum =
      IFDEF VERBOSE_EXN THEN
         if !debug_refiner then
            eprintf "Refiner.add_rewrite: %s%t" name eflush
      ENDIF;
      let { build_opname = opname; build_refiner = refiner } = build in
      let rw = Rewrite.term_rewrite ar0_ar0 [redex] [contractum] in
      let opname = mk_opname name opname in
      let ref_rewrite =
         { rw_name = opname;
           rw_rewrite = redex, contractum;
           rw_refiner = refiner
         }
      in
      let refiner' = RewriteRefiner ref_rewrite in
      let rw sent t =
         match apply_rewrite rw ar0_ar0_null t [] with
            [t'], _ ->
               sent.sent_rewrite ref_rewrite;
               t', RewriteHere opname
          | [], _ ->
               raise (Failure "Refine.add_rewrite: no contracta")
          | _ ->
               raise (Failure "Refine.add_Rewrite: multiple contracta")
      in
         refiner', (rw : prim_rewrite)

   let add_prim_rewrite build name redex contractum =
      IFDEF VERBOSE_EXN THEN
         if !debug_refiner then
            eprintf "Refiner.add_prim_rewrite: %s%t" name eflush
      ENDIF;
      let { build_opname = opname; build_refiner = refiner } = build in
         match find_refiner refiner (mk_opname name opname) with
            RewriteRefiner rw ->
               let { rw_rewrite = redex', contractum' } = rw in
               let term1 = mk_xlist_term [redex; contractum] in
               let term2 = mk_xlist_term [redex'; contractum'] in
                  if alpha_equal term1 term2 then
                     PrimRewriteRefiner { prw_rewrite = rw;
                                          prw_refiner = refiner;
                                          prw_proof = Extracted ()
                     }
                  else
                     REF_RAISE(RefineError (name, StringError "not a rewrite"))
          | _ ->
               REF_RAISE(RefineError (name, StringError "not a rewrite"))

   let add_delayed_rewrite build name redex contractum ext =
      IFDEF VERBOSE_EXN THEN
         if !debug_refiner then
            eprintf "Refiner.add_delayed_rewrite: %s%t" name eflush
      ENDIF;
      let { build_opname = opname; build_refiner = refiner } = build in
         match find_refiner refiner (mk_opname name opname) with
            RewriteRefiner rw ->
               let compute_ext () =
                  let { rw_rewrite = redex, contractum } = rw in
                  let ext = ext () in
                  let { ext_goal = goal; ext_subgoals = subgoals } = ext in
                  let t =
                     match goal, subgoals with
                        { mseq_goal = goal; mseq_hyps = [] },
                        [{ mseq_goal = subgoal; mseq_hyps = [] }] ->
                           if alpha_equal goal redex & alpha_equal subgoal contractum then
                              term_of_extract refiner ext []
                           else
                              REF_RAISE(RefineError (name, StringError "extract does not match"))
                      | _ ->
                           REF_RAISE(RefineError (name, StringError "bogus proof"))
                  in
                     ()
               in
                  PrimRewriteRefiner { prw_proof = Delayed compute_ext;
                                       prw_rewrite = rw;
                                       prw_refiner = refiner
                  }
          | _ ->
               REF_RAISE(RefineError (name, StringError "not a rewrite"))

   (************************************************************************
    * CONDITIONAL REWRITE                                                  *
    ************************************************************************)

   (*
    * Conditional rewrite.
    *)
   let add_cond_rewrite build name vars params subgoals redex contractum =
      IFDEF VERBOSE_EXN THEN
         if !debug_refiner then
            eprintf "Refiner.add_cond_rewrite: %s%t" name eflush
      ENDIF;
      let { build_opname = opname; build_refiner = refiner } = build in
      let rw = Rewrite.term_rewrite ([||], vars) (redex::params) (contractum :: subgoals) in
      let opname = mk_opname name opname in
      let ref_crw =
         { crw_name = opname;
           crw_count = List.length subgoals;
           crw_rewrite = subgoals, redex, contractum;
           crw_refiner = refiner
         }
      in
      let refiner' = CondRewriteRefiner ref_crw in
      let rw' (vars, params) (sent : sentinal) (bvars : string list list) seq t =
         (* BUG: is alpha variance compute correctly by replace_goal? *)
         match apply_rewrite rw ([||], vars, bvars) t params with
            (t' :: subgoals), names ->
               let subgoals' = List.map (replace_goal seq) subgoals in
                  sent.sent_cond_rewrite ref_crw;
                  t',
                  subgoals',
                  SingleJust { ext_names = names;
                               ext_params = params;
                               ext_refiner = opname
                  }
             | [], _ ->
                  raise (Failure "Refine.add_cond_rewrite: no contracta")
      in
         refiner', (rw' : prim_cond_rewrite)

   let add_prim_cond_rewrite build name vars params subgoals redex contractum =
      IFDEF VERBOSE_EXN THEN
         if !debug_refiner then
            eprintf "Refiner.add_prim_cond_rewrite: %s%t" name eflush
      ENDIF;
      let { build_opname = opname; build_refiner = refiner } = build in
         match find_refiner refiner (mk_opname name opname) with
            CondRewriteRefiner crw ->
               let { crw_rewrite = subgoals', redex', contractum' } = crw in
               let term1 = mk_xlist_term (redex :: contractum :: subgoals) in
               let term2 = mk_xlist_term (redex' ::  contractum' :: subgoals') in
                  if alpha_equal term1 term2 then
                     PrimCondRewriteRefiner { pcrw_proof = Extracted ();
                                              pcrw_rewrite = crw;
                                              pcrw_refiner = refiner
                     }
                  else
                     REF_RAISE(RefineError (name, StringError "not a conditional rewrite"))
          | _ ->
               REF_RAISE(RefineError (name, StringError "not a conditional rewrite"))

   let add_delayed_cond_rewrite build name vars params subgoals redex contractum ext =
      IFDEF VERBOSE_EXN THEN
         if !debug_refiner then
            eprintf "Refiner.add_delayed_cond_rewrite: %s%t" name eflush
      ENDIF;
      let { build_opname = opname; build_refiner = refiner } = build in
         match find_refiner refiner (mk_opname name opname) with
            CondRewriteRefiner crw ->
               let compute_ext () =
                  let ext = ext () in
                  let { ext_goal = goal; ext_subgoals = subgoals' } = ext in
                  let { mseq_goal = goal; mseq_hyps = goal_hyps } = goal in
                  let subgoals', sub_hyps = split_msequent_list subgoals' in
                  let { crw_rewrite = subgoals, redex, contractum } = crw in
                  let redex = replace_goal goal redex in
                  let contractum = replace_goal goal contractum in
                  let subgoals = List.map (replace_goal goal) subgoals in
                     if equal_hyps goal_hyps sub_hyps &
                        List_util.for_all2 alpha_equal (redex :: contractum :: subgoals) (goal :: subgoals)
                     then
                        let _ = term_of_extract refiner ext []
                        in ()
                     else
                        REF_RAISE(RefineError (name, StringError "derivation does not match"))
               in
                  PrimCondRewriteRefiner { pcrw_proof = Delayed compute_ext;
                                           pcrw_rewrite = crw;
                                           pcrw_refiner = refiner
                  }
          | _ ->
               REF_RAISE(RefineError (name, StringError "not a conditional rewrite"))

   (*
    * An ML rewrite.
    *)
   let add_ml_rewrite build name info =
      IFDEF VERBOSE_EXN THEN
         if !debug_refiner then
            eprintf "Refiner.add_cond_rewrite: %s%t" name eflush
      ENDIF;
      let { ml_rewrite_rewrite = rw } = info in
      let { build_opname = opname; build_refiner = refiner } = build in
      let opname = mk_opname name opname in
      let ref_crw =
         { ml_rw_name = opname;
           ml_rw_info = info;
           ml_rw_refiner = refiner
         }
      in
      let refiner' = MLRewriteRefiner ref_crw in
      let rw (vars, params) (sent : sentinal) (bvars : string list list) seq t =
         let t, subgoals, names = rw vars bvars params seq t in
            sent.sent_ml_rewrite ref_crw;
            t,
            subgoals,
            SingleJust { ext_names = names;
                         ext_params = params;
                         ext_refiner = opname
            }
      in
         refiner', (rw : prim_cond_rewrite)

   (************************************************************************
    * API FUNCTIONS                                                        *
    ************************************************************************)

   (*
    * Axiom creation.
    *)
   let create_axiom build name term =
      let refiner, tac = add_axiom build name term in
         build.build_refiner <- refiner;
         (tac : prim_tactic)

   let prim_axiom build name term =
      build.build_refiner <- add_prim_axiom build name term

   let delayed_axiom build name extf =
      build.build_refiner <- add_delayed_axiom build name extf

   let derived_axiom build name ext =
      let extf () = ext in
      let refiner = add_delayed_axiom build name extf in
         check refiner;
         build.build_refiner <- refiner

   (*
    * Rules.
    *)
   let create_rule build name addrs names params mterm =
      let refiner, tac = add_rule build name addrs names params mterm in
         build.build_refiner <- refiner;
         tac

   let prim_rule build name vars params args result =
      build.build_refiner <-  add_prim_rule build name vars params args result

   let delayed_rule build name vars params args extf =
      build.build_refiner <- add_delayed_rule build name vars params args extf

   let derived_rule build name vars params args ext =
      let extf () = ext in
      let refiner = add_delayed_rule build name vars params args extf in
         check refiner;
         build.build_refiner <- refiner

   let create_ml_rule build name mlr =
      let refiner, tac = add_ml_rule build name mlr in
         build.build_refiner <- refiner;
         tac

   (*
    * Rewrites.
    *)
   let create_rewrite build name redex contractum =
      let refiner, rw = add_rewrite build name redex contractum in
         build.build_refiner <- refiner;
         rw

   let prim_rewrite build name redex contractum =
      build.build_refiner <- add_prim_rewrite build name redex contractum

   let delayed_rewrite build name redex contractum extf =
      build.build_refiner <- add_delayed_rewrite build name redex contractum extf

   let derived_rewrite build name redex contractum ext =
      let extf () = ext in
      let refiner = add_delayed_rewrite build name redex contractum extf in
         check refiner;
         build.build_refiner <- refiner

   (*
    * Condiitional rewrites.
    *)
   let create_cond_rewrite build name vars params args redex contractum =
      let refiner, rw = add_cond_rewrite build name vars params args redex contractum in
         build.build_refiner <- refiner;
         (rw : prim_cond_rewrite)

   let prim_cond_rewrite build name vars params args redex contractum =
      build.build_refiner <- add_prim_cond_rewrite build name vars params args redex contractum

   let delayed_cond_rewrite build name vars params args redex contractum extf =
      build.build_refiner <- add_delayed_cond_rewrite build name vars params args redex contractum extf

   let derived_cond_rewrite build name vars params args redex contractum ext =
      let extf () = ext in
      let refiner = add_delayed_cond_rewrite build name vars params args redex contractum extf in
         check refiner;
         build.build_refiner <- refiner

   let create_ml_rewrite build name rw =
      let refiner, rw' = add_ml_rewrite build name rw in
         build.build_refiner <- refiner;
         (rw' : prim_cond_rewrite)

   (************************************************************************
    * DESTRUCTORS                                                          *
    ************************************************************************)

   (*
    * Null refiners.
    *)
   let is_null_refiner = function
      NullRefiner -> true
    | _ -> false

   (*
    * Get the next item from a refiner.
    *)
   let dest_refiner = function
      NullRefiner ->
         raise (Invalid_argument "dest_refiner")

    | AxiomRefiner { axiom_name = n; axiom_term = t; axiom_refiner = r } ->
         RIAxiom { ri_axiom_name = n; ri_axiom_term = t }, r
    | PrimAxiomRefiner { pax_axiom = ax; pax_refiner = r } ->
         RIPrimTheorem { ri_pthm_axiom = AxiomRefiner ax }, r

    | RuleRefiner { rule_name = n; rule_rule = t; rule_refiner = r } ->
         RIRule { ri_rule_name = n; ri_rule_rule = t }, r
    | MLRuleRefiner { ml_rule_name = cond; ml_rule_refiner = r } ->
         RIMLRule { ri_ml_rule_name = cond }, r
    | PrimRuleRefiner { prule_rule = rule; prule_refiner = r } ->
         RIPrimTheorem { ri_pthm_axiom = RuleRefiner rule }, r

    | RewriteRefiner { rw_name = n; rw_rewrite = redex, con; rw_refiner = r } ->
         RIRewrite { ri_rw_name = n;
                     ri_rw_redex = redex;
                     ri_rw_contractum = con
         }, r
    | PrimRewriteRefiner { prw_rewrite = r1; prw_refiner = r2 } ->
         RIPrimRewrite { ri_prw_rewrite = RewriteRefiner r1 }, r2

    | CondRewriteRefiner { crw_name = n; crw_rewrite = conds, redex, con; crw_refiner = r } ->
         RICondRewrite { ri_crw_name = n;
                         ri_crw_conds = conds;
                         ri_crw_redex = redex;
                         ri_crw_contractum = con
         },
         r
    | PrimCondRewriteRefiner { pcrw_rewrite = r1; pcrw_refiner = r2 } ->
         RIPrimRewrite { ri_prw_rewrite = CondRewriteRefiner r1 }, r2
    | MLRewriteRefiner { ml_rw_name = n; ml_rw_refiner = r } ->
         RIMLRewrite { ri_ml_rw_name = n }, r

    | PairRefiner (par, r) ->
         RIParent par, r
    | ListRefiner refs ->
         (* List are never constructed by the user *)
         raise (Invalid_argument "dest_refiner")
    | LabelRefiner (name, r) ->
         RILabel name, r
end

