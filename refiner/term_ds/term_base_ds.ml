(*
 * This is the module that implements delayed substitution,
 * keeps track of free variables and does some sharing.
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Alexey Nogin, Cornell University
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
 * Authors: Alexey Nogin
 *)

#include "refine_error.h"

open Printf
open Mp_debug
open Opname
open Refine_error_sig
open Term_ds

(*
 * Show the file loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Term_ds%t" eflush

let debug_subst =
   create_debug (**)
      { debug_name = "subst";
        debug_description = "Display substition operations";
        debug_value = false
      }

let debug_fv =
   create_debug (**)
      { debug_name = "free_vars";
        debug_description = "Display free variables calculation";
        debug_value = false
      }

module Term
   (RefineError : RefineErrorSig
    with type level_exp = TermType.level_exp
    with type param = TermType.param
    with type term = TermType.term
    with type bound_term = TermType.bound_term)
=
struct
   (************************************************************************
    * Type definitions                                                     *
    ************************************************************************)

   open TermType
   open RefineError

   type level_exp_var = TermType.level_exp_var
   type level_exp = TermType.level_exp
   type param = TermType.param
   type operator = TermType.operator
   type term = TermType.term
   type term_core = TermType.term_core
   type bound_term = TermType.bound_term
   type esequent = TermType.esequent
   type seq_hyps = TermType.seq_hyps
   type seq_goals = TermType.seq_goals
   type string_set = TermType.StringSet.t

   type hypothesis = TermType.hypothesis
   type level_exp_var' = TermType.level_exp_var'
   type level_exp' = TermType.level_exp'
   type object_id = TermType.object_id
   type param' = TermType.param'
   type operator' = TermType.operator'
   type term' = TermType.term'
   type bound_term' = TermType.bound_term'

   (*
    * Simple substitution.
    *)
   type term_subst = (string * term) list

   module SeqHypType =
   struct
      type t = hypothesis
   end

   module SeqGoalType =
   struct
      type t = term
   end

   module SeqHyp = SEQ_SET.Make (SeqHypType)
   module SeqGoal = SEQ_SET.Make (SeqGoalType)

   (************************************************************************
    * DEBUGGING                                                            *
    ************************************************************************)

   (*
    * Printer is installed by client.
    *)
   let print_term_ref = ref (fun _ _ -> raise (Failure "Term_ds.print_term: printer not installed"))

   let debug_print out t =
      !print_term_ref out t

   let print_term = debug_print

   let rec print_term_list out = function
      [t] ->
         debug_print out t
    | h::t ->
         debug_print out h;
         output_string out ", ";
         print_term_list out t
    | [] ->
         ()

   let install_debug_printer f =
      print_term_ref := f

   (************************************************************************
    * Free variables, substitution                                         *
    ************************************************************************)

   let rec term_free_vars t =
      match t.free_vars with
         Vars vars -> vars
       | VarsDelayed ->
            let vars =
               match t.core with
                  FOVar v -> StringSet.make v
                | Term t' -> 
#ifdef VERBOSE_EXN
                     if !debug_fv then
                        eprintf "Request for Term fvs: Term: %a%t" debug_print t eflush;
                     let res =
#endif
                     bterms_free_vars t'.term_terms
#ifdef VERBOSE_EXN
                     in
                        if !debug_fv then begin
                           eprintf "Result: ";
                           List.iter (eprintf "%s ") (StringSet.elements res);
                           eprintf "%t" eflush;
                        end; res
#endif
                | Sequent seq ->
                     StringSet.union
                        (term_free_vars seq.sequent_args)
                        (hyp_fv
                           seq.sequent_hyps
                           (SeqHyp.length seq.sequent_hyps - 1)
                           (goal_fv seq.sequent_goals (SeqGoal.length seq.sequent_goals - 1)))
                | Subst (t,sub) ->
#ifdef VERBOSE_EXN
                     if !debug_fv then begin
                        eprintf "Request for Subst fvs: Term: %a; Subst: " debug_print t;
                        List.iter (fun (v,t) -> eprintf "(%s : %a) " v debug_print t) sub;
                        eprintf "%t" eflush;
                     end;
                     let res =
#endif
                     StringSet.union
                        (List.fold_right
                           StringSet.remove
                           (List_util.fst_split sub)
                           (term_free_vars t))
                        (subst_free_vars sub)
#ifdef VERBOSE_EXN
                     in 
                        if !debug_fv then begin
                           eprintf "Result: ";
                           List.iter (eprintf "%s ") (StringSet.elements res);
                           eprintf "%t" eflush;
                        end; res
#endif
            in t.free_vars <- Vars vars; vars

   and bterm_free_vars bt =
      List.fold_right StringSet.remove bt.bvars (term_free_vars bt.bterm)

   and bterms_free_vars = function
      [] -> StringSet.empty
    | [bt] -> bterm_free_vars bt
    | bt::tl -> StringSet.union (bterms_free_vars tl) (bterm_free_vars bt)

   and goal_fv goals i =
      if i < 0 then StringSet.empty else
      StringSet.union (term_free_vars (SeqGoal.get goals i)) (goal_fv goals (pred i))

   and terms_free_vars = function
      [] -> StringSet.empty
    | [t] -> term_free_vars t
    | t::tl -> StringSet.union (terms_free_vars tl) (term_free_vars t)

   and hyp_fv hyps i fvs =
      if i < 0 then fvs else
      hyp_fv hyps (pred i) (
      match SeqHyp.get hyps i with
         Hypothesis (v,t) ->
            StringSet.union (term_free_vars t) (StringSet.remove v fvs)
       | Context (v,subterms) ->
            StringSet.union fvs (terms_free_vars subterms))

   and subst_free_vars = function
      [] -> StringSet.empty
    | [(v,t)] -> term_free_vars t
    | (v,t)::tl -> StringSet.union (subst_free_vars tl) (term_free_vars t)

   let do_term_subst sub t =
#ifdef VERBOSE_EXN
      if !debug_subst then
         begin
            debug_subst := false;
            eprintf "do_term_subst: { %a\n" debug_print t;
            eprintf "\tfree_vars:";
            List.iter (fun name -> eprintf " %s" name) (StringSet.elements (term_free_vars t));
            eflush stderr;
            if sub == [] then eprintf "\t empty substitution\n" else
            List.iter (fun (v, t) -> eprintf "\t%s: %a\n" v debug_print t) sub;
            eprintf "}%t" eflush;
            debug_subst := true
         end;
#endif
      match StringSet.fst_mem_filt (term_free_vars t) sub with
         [] -> t
       | sub' ->
            {free_vars = VarsDelayed; core = Subst (t,sub')}

   let rec filter_sub_vars bvars = function
      [] -> []
    | (((v,t) as sb)::tail) as l ->
         if (List.mem v bvars) then filter_sub_vars bvars tail
         else
            let ftail = filter_sub_vars bvars tail in
            if ftail == tail then l else sb::ftail

   let do_bterm_subst sub bt =
      if (bt.bvars==[]) then
         { bvars = []; bterm = do_term_subst sub bt.bterm }
      else
         { bvars = bt.bvars; bterm = 
           do_term_subst (filter_sub_vars bt.bvars sub) bt.bterm }

   (************************************************************************
    * De/Constructors                                                 *
    ************************************************************************)

   let var_opname = make_opname ["var"]

   (*
    * Manifest terms are injected into the "perv" module.
    *)
   let xperv = make_opname ["Perv"]
   let sequent_opname = mk_opname "sequent" xperv

   (************************************************************************
    * De/Constructors                                                 *
    ************************************************************************)

   let fail_core s =
      raise (Invalid_argument ("Term_ds." ^ s ^ ": get_core returned a Subst"))

   let rec subst_remove v = function
      [] -> []
    | ((v',t)::tl) as sub ->
         if (v = v') then subst_remove v tl
         else let rem = subst_remove v tl in
            if rem == tl then sub else (v',t)::rem

   let rec get_core t =
      match t.core with
         Subst (tt,sub) ->
            let core =
               match get_core tt with
                  FOVar v ->
                     (* since sub was not eliminated, v should be in sub *)
                     let new_term = List.assoc v sub in
                        get_core (new_term)
                | Term ttt ->
                     Term { term_op = ttt.term_op;
                            term_terms = List.map (do_bterm_subst sub) ttt.term_terms }
                | Sequent { sequent_args = args;
                            sequent_hyps = hyps;
                            sequent_goals = goals } ->
                     Sequent { sequent_args = do_term_subst sub args;
                               sequent_hyps = SeqHyp.lazy_apply (hyps_subst sub) hyps;
                               sequent_goals = SeqGoal.lazy_apply (do_term_subst sub) goals }
                | Subst _ -> fail_core "get_core"
            in
               t.core <- core;
               core
       | core -> core

   and hyps_subst sub = function
      Hypothesis (v,t) ->
         Hypothesis (v,do_term_subst sub t)
    | Context (v,ts) ->
         Context (v, List.map (do_term_subst sub) ts)

   (*
    * Make a variable.
    *)
   let mk_var_term v =
      { free_vars = VarsDelayed;
        core = FOVar v }

   let mk_op name params = { op_name = name; op_params = params }

   let mk_simple_bterm term =
      { bvars = []; bterm = term }

   let make_bterm x = x (* external make_bterm : bound_term -> bound_term = "%identity" *)

   let mk_bterm vars term =
      { bvars = vars; bterm = term }

   let rec dest_term t =
      match t.core with
         Term t -> t
       | Sequent _ ->
            raise (Invalid_argument "Term_base_ds.dest_term: dest_term called on a sequent")
       | FOVar v -> 
             { term_op = { op_name = var_opname; op_params = [Var v] }; term_terms = [] }
       | Subst _ -> let _ = get_core t in dest_term t

   (*
    * New variable production.
    * renames are the variables to be renamed,
    * and av is a list list of variables to avoid.
    * Our algorithm is slow and simple: just append an
    * index and increment until no more collisions.
    *)

   let rec new_var av v i =
      let v' = v ^ "_" ^ (string_of_int i) in
      if (StringSet.mem av v')
         then new_var av v (succ i)
         else v'

   and new_vars av = function
      [] -> ([],[])
    | v::vt ->
         let (vs,ts) = (new_vars av vt) in
         let v' = new_var av v 0 in
            ((v,v')::vs, (v,mk_var_term v')::ts)

   let dest_bterm x = x (* external dest_bterm : bound_term -> bound_term = "%identity" *)

   let mk_sequent_term seq =
      { free_vars = VarsDelayed; core = Sequent seq }

   let rec no_bvars = function
      [] -> true
    | bt::btrms -> bt.bvars == [] && no_bvars btrms

   let dest_simple_bterm = function
      { bvars = []; bterm = tt } -> tt
    | _ -> ref_raise(RefineError ("dest_simple_bterm", StringError "bvars exist"))

   let make_term = function
      { term_op = { op_name = opname; op_params = [Var v] };
        term_terms = []
      } when Opname.eq opname var_opname ->
         {free_vars = VarsDelayed; core = FOVar v}
    | t ->
         {free_vars = VarsDelayed; core = Term t}

   let mk_term op bterms =
      match op,bterms with
         { op_name = opname; op_params = [Var v] },[] when Opname.eq opname var_opname ->
            {free_vars = VarsDelayed; core = FOVar v }
       | _ ->
            { free_vars = VarsDelayed;
              core = Term { term_op = op; term_terms = bterms }}

   (*
    * Second order context, contains a context term, plus
    * binding variables like so vars.
    *)
   let context_opname = make_opname ["context"]

   let is_context_term t =
      match dest_term t with
         { term_op = { op_name = opname; op_params = [Var _] };
           term_terms = bterms
         } when Opname.eq opname context_opname ->
            bterms <> [] & no_bvars bterms
       | _ ->
            false

   let dest_context term =
      match dest_term term with
         { term_op = { op_name = opname; op_params = [Var v] };
           term_terms = bterms
         } when Opname.eq opname context_opname ->
            let rec collect term = function
               [bterm] ->
                  [], dest_simple_bterm bterm
             | bterm::bterms ->
                  let args, term = collect term bterms in
                     dest_simple_bterm bterm :: args, term
             | _ ->
                  ref_raise(RefineError ("dest_context", TermMatchError (term, "not a context")))
            in
            let args, term = collect term bterms in
               v, term, args
       | _ ->
            ref_raise(RefineError ("dest_context", TermMatchError (term, "not a context")))

   let mk_context_term v term terms =
      let rec collect term = function
         [] ->
            [mk_simple_bterm term]
       | h::t ->
            mk_simple_bterm h :: collect term t
      in
      let op = { op_name = context_opname; op_params = [Var v] } in
         mk_term op (collect term terms)

   let mk_level_var v i =
      { le_var = v; le_offset = i }

   let mk_level i l =
      { le_const = i; le_vars = l }

   let subterms_of_term t =
      List.map (fun bt -> bt.bterm) (dest_term t).term_terms

   let subterm_count t =
      List.length (dest_term t).term_terms

   let subterm_arities_aux bterm = List.length bterm.bvars

   let subterm_arities term =
         List.map subterm_arities_aux (dest_term term).term_terms
   (*
    * Operator names.
    *)
   let rec opname_of_term t = match t.core with
      Term t -> t.term_op.op_name
    | Sequent _ -> sequent_opname
    | FOVar _ -> var_opname
    | Subst _ -> let _ = get_core t in opname_of_term t

   (* These are trivial identity functions *)

   let make_op x = x (* external make_op : operator' -> operator = "%identity" *)
   let dest_op x = x (* external dest_op : operator -> operator' = "%identity" *)
   let make_param x = x (* external make_param : param' -> param = "%identity" *)
   let dest_param x = x (* external dest_param : param -> param' = "%identity" *)
   let make_level x = x (* external make_level : level_exp' -> level_exp = "%identity" *)
   let dest_level x = x (* external dest_level : level_exp -> level_exp' = "%identity" *)
   let make_level_var x = x (* external make_level_var : level_exp_var' -> level_exp_var = "%identity" *)
   let dest_level_var x = x (* external dest_level_var : level_exp_var -> level_exp_var' = "%identity" *)
   let make_object_id x = x (* external make_object_id : param list -> object_id = "%identity" *)
   let dest_object_id x = x (* external dest_object_id : object_id -> param list = "%identity" *)

   (************************************************************************
    * Variables                                                            *
    ************************************************************************)

   (*
    * See if a term is a variable.
    *)

   let rec is_var_term t =
      match t.core with
         FOVar _ -> true
       | Subst _ -> let _ = get_core t in is_var_term t
       | _ -> false

   (*
    * Destructor for a variable.
    *)
   let rec dest_var t =
      match t.core with
         FOVar v -> v
       | Subst _ -> let _ = get_core t in dest_var t
       | _ -> ref_raise(RefineError ("dest_var", TermMatchError (t, "not a var")))

   (*
    * Second order variables have subterms.
    *)
   let is_so_var_term t = match get_core t with
      FOVar _ -> true
    | Term { term_op = { op_name = opname; op_params = [Var _] };
             term_terms = terms } -> 
         Opname.eq opname var_opname && no_bvars terms
    | _ -> false

   let dest_so_var t = match get_core t with
      FOVar v -> v,[]
    | Term { term_op = { op_name = opname; op_params = [Var v] };
             term_terms = terms } when Opname.eq opname var_opname ->
         v, List.map dest_simple_bterm terms
    | _ -> ref_raise(RefineError ("dest_so_var", TermMatchError (t, "not a so_var")))

   (*
    * Second order variable.
    *)
   let mk_so_var_term v terms =
      { free_vars = VarsDelayed; 
        core = Term { term_op = { op_name = var_opname; op_params = [Var v] };
                      term_terms = List.map mk_simple_bterm terms }
        }

   (*
    * Second order context, contains a context term, plus
    * binding variables like so vars.
    *)
   let context_opname = make_opname ["context"]

   let is_context_term t =
      match get_core t with
         Term { term_op = { op_name = opname; op_params = [Var _] };
                term_terms = bterms
              } when Opname.eq opname context_opname ->
            bterms <> [] & no_bvars bterms
       | _ ->
            false

   let dest_context term =
      match dest_term term with
         { term_op = { op_name = opname; op_params = [Var v] };
           term_terms = bterms
         } when Opname.eq opname context_opname ->
            let rec collect term = function
               [bterm] ->
                  [], dest_simple_bterm bterm
             | bterm::bterms ->
                  let args, term = collect term bterms in
                     dest_simple_bterm bterm :: args, term
             | _ ->
                  ref_raise(RefineError ("dest_context", TermMatchError (term, "not a context")))
            in
            let args, term = collect term bterms in
               v, term, args
       | _ ->
            ref_raise(RefineError ("dest_context", TermMatchError (term, "not a context")))

   let mk_context_term v term terms =
      let rec collect term = function
         [] ->
            [mk_simple_bterm term]
       | h::t ->
            mk_simple_bterm h :: collect term t
      in
      let op = { op_name = context_opname; op_params = [Var v] } in
         mk_term op (collect term terms)

   (************************************************************************
    * Tools for "simple" terms                                             *
    ************************************************************************)

   (*
    * "Simple" terms have no parameters and no binding variables.
    *)
   let is_simple_term_opname name t = match get_core t with
      Term { term_op = { op_name = name'; op_params = [] };
             term_terms = bterms
           } when Opname.eq name' name -> no_bvars bterms
    | _ -> false

   let mk_any_term op terms = mk_term op (List.map mk_simple_bterm terms)

   let mk_simple_term name terms =
      mk_any_term { op_name = name; op_params = [] } terms

   let dest_simple_term t = match dest_term t with
      { term_op = { op_name = name; op_params = [] };
         term_terms = bterms } ->
            name, List.map dest_simple_bterm bterms
    | _ -> ref_raise(RefineError ("dest_simple_term", TermMatchError (t, "params exist")))

   let dest_simple_term_opname name t = match dest_term t with
      { term_op = { op_name = name'; op_params = [] };
         term_terms = bterms } ->
         if Opname.eq name name' then List.map dest_simple_bterm bterms
         else
            ref_raise(RefineError ("dest_simple_term_opname", TermMatchError (t, "opname mismatch")))
    | _ -> ref_raise(RefineError ("dest_simple_term_opname", TermMatchError (t, "params exist")))
end
