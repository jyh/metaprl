doc <:doc<
   Provability in a sequent logic.
   @docoff

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2005 Mojave Group, Caltech

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
   @end[license]

   @parents
>>
extends Itt_hoas_bterm_wf
extends Itt_hoas_proof
extends Itt_hoas_sequent
extends Itt_hoas_sequent_term
extends Itt_hoas_sequent_proof_step

doc docoff

open Lm_num
open Lm_debug
open Lm_printf
open Lm_int_set
open Basic_tactics
open Simple_print
open Itt_list
open Itt_bool
open Itt_dfun
open Itt_dprod
open Itt_logic
open Itt_struct
open Itt_int_base
open Itt_hoas_base
open Itt_hoas_vbind
open Itt_hoas_vector
open Itt_hoas_proof
open Itt_hoas_sequent
open Itt_hoas_sequent_term
open Itt_hoas_sequent_proof_step
open Itt_hoas_normalize
open Itt_hoas_bterm_wf

let debug_sequent_proof =
   create_debug (**)
      { debug_name = "sequent_proof";
        debug_description = "Debug Itt_hoas_sequent_proof tactics";
        debug_value = false
      }

doc <:doc<
   Provability in a sequent logic.
>>
define unfold_Provable_sequent : Provable{'logic; 'seq} <--> <:xterm<
   (seq in Sequent) && Provable{Sequent; logic; seq}
>>

(************************************************************************
 * Well-formedness.
 *)
doc <:doc<
   Well-formedness.
>>
interactive provable_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- logic in Logic{Sequent} -->
   "wf" : <H> >- seq in Sequent -->
   <H> >- Provable{logic; seq} Type
>>

(************************************************************************
 * Intro rules.
 *)
doc <:doc<
   A @tt[Provable] judgment intro rule is provable if it can be refined
   by a rule in the logic.  Unfortunately, we have to provide the witness
   eagerly.  However, it should be easy to do so.
>>
interactive provable_intro 'premises : <:xrule<
   "wf" : <H> >- logic in Logic{Sequent} -->
   "wf" : <H> >- premises in list{Sequent} -->
   "wf" : <H> >- goal in Sequent -->
   "aux" : <H> >- all_list{premises; premise. Provable{logic; premise}} -->
   <H> >- exists witness: ProofStepWitness. SimpleStep{premises; goal; witness; logic} -->
   <H> >- Provable{logic; goal}
>>

doc <:doc<
   Use an explicit rule to decompose the << SimpleStep{'premises; 'goal; 'witness; 'logic} >>.
>>
interactive simple_step_intro 'step : <:xrule<
   "wf" : <H> >- logic in Logic{Sequent} -->
   "wf" : <H> >- premises in list{Sequent} -->
   "wf" : <H> >- goal in Sequent -->
   "wf" : <H> >- step in ProofRule{Sequent} -->
   "wf" : <H> >- MemLogic{Sequent; step; logic} -->
   <H> >- exists witness: ProofStepWitness. "assert"{step (proof_step{premises; goal}, witness)} -->
   <H> >- exists witness: ProofStepWitness. SimpleStep{premises; goal; witness; logic}
>>

(************************************************************************
 * Forward chaining.
 *)
doc <:doc<
   Forward-chaining rules, mainly for well-formedness reasoning.
>>
interactive provable_forward 'H : <:xrule<
   <H>; Provable{logic; seq}; <J>; seq in Sequent >- C -->
   <H>; Provable{logic; seq}; <J> >- C
>>

let provable_forwardT i =
   provable_forward i
   thenT rw normalizeBTermC (-1)

let resource forward +=
   [<< Provable{'logic; 'seq} >>, { forward_loc = (LOCATION); forward_prec = forward_trivial_prec; forward_tac = provable_forwardT }]

(************************************************************************
 * Tactics.
 *)
doc docoff

let provable_sequent_term = << Provable{'logic; 'seq} >>
let provable_sequent_opname = opname_of_term provable_sequent_term
let is_provable_sequent_term = is_dep0_dep0_term provable_sequent_opname
let dest_provable_sequent_term = dest_dep0_dep0_term provable_sequent_opname

let it_term = << it >>
let xconcl_term = << xconcl >>
let vbind_arg_term = << vbind >>
let hyplist_arg_term = << hyplist >>
let hyp_context_arg_term = << hyp_context >>

let mk_hyplist_term v cvars args =
   let seq =
      { sequent_args = hyplist_arg_term;
        sequent_hyps = SeqHyp.singleton (Context (v, cvars, args));
        sequent_concl = xconcl_term
      }
   in
      mk_sequent_term seq

(*
 * Build a vector of it terms.
 *)
let mk_it_vector len =
   let rec collect l i =
      if i = len then
         l
      else
         collect (it_term :: l) (succ i)
   in
      collect [] 0

(*
 * Collect information about all second-order vars and contexts
 * in a term.
 *)
let rec socvars_info info t =
   if is_var_term t then
      info
   else if is_so_var_term t then
      socvars_so_var_info info t
   else if is_context_term t then
      socvars_context_info info t
   else if is_sequent_term t then
      socvars_sequent_info info t
   else
      socvars_bterms_info info (dest_term t).term_terms

and socvars_terms_info info tl =
   List.fold_left socvars_info info tl

and socvars_bterm_info info bt =
   socvars_info info (dest_bterm bt).bterm

and socvars_bterms_info info btl =
   List.fold_left socvars_bterm_info info btl

and socvars_so_var_info (cinfo, soinfo) t =
   let v, cvars, args = dest_so_var t in
   let soinfo = SymbolTable.add soinfo v (cvars, List.length args) in
      socvars_terms_info (cinfo, soinfo) args

and socvars_context_info info t =
   let _, t, _, args = dest_context t in
   let info = socvars_info info t in
      socvars_terms_info info args

and socvars_sequent_info info t =
   let { sequent_hyps = hyps;
         sequent_concl = concl
       } = explode_sequent t
   in
   let info =
      SeqHyp.fold (fun info _ h ->
            match h with
               Hypothesis (_, t) ->
                  socvars_info info t
             | Context (v, cvars, args) ->
                  let cinfo, soinfo = info in
                  let cinfo = SymbolTable.add cinfo v (cvars, List.length args) in
                     socvars_terms_info (cinfo, soinfo) args) info hyps
   in
      socvars_info info concl

(*
 * Get the variable ordering in the proof witness.
 *)
let rec find_var_index cindex soindex t =
   if is_exists_term t then
      let _, _, t = dest_exists t in
         find_var_index cindex soindex t
   else if is_assert_term t then
      find_var_index cindex soindex (dest_assert t)
   else if is_let_cvar_term t then
      let _, _, i, v, t = dest_let_cvar_term t in
      let i = int_of_num (dest_number i) in
      let cindex = IntTable.add cindex i v in
         find_var_index cindex soindex t
   else if is_let_sovar_term t then
      let _, _, i, v, t = dest_let_sovar_term t in
      let i = int_of_num (dest_number i) in
      let soindex = IntTable.add soindex i v in
         find_var_index cindex soindex t
   else
      cindex, soindex

(*
 * Build the context hypotheses.
 *)
let build_bind_context cinfo cvars arity =
   (* Add the contexts to the hyp list *)
   let hyps =
      List.fold_left (fun hyps v ->
            try
               let cvars, arity = SymbolTable.find cinfo v in
                  Context (v, cvars, mk_it_vector arity) :: hyps
            with
               Not_found ->
                  hyps) [] cvars
   in

   (* Add scalar hyps *)
   let rec add_scalar_hyps hyps vars i =
      if i = arity then
         vars, hyps
      else
         let v = Lm_symbol.make "x" i in
         let vars = mk_var_term v :: vars in
         let hyps = Hypothesis (v, it_term) :: hyps in
            add_scalar_hyps hyps vars (succ i)
   in
   let vars, hyps = add_scalar_hyps hyps [] 0 in
   let vars = List.rev vars in
   let hyps = List.rev hyps in
      vars, hyps

(*
 * Build the second-order witness.
 *)
let build_so_witness cinfo soinfo sindex =
   let witness, _ =
      IntTable.fold (fun (witness, index) index' v ->
            if index' <> index then
               raise (RefineError ("Itt_hoas_sequent_proof.build_so_witness", StringIntError ("witness ordering error", index')));

            (* Info for the var *)
            let cvars, arity =
               try SymbolTable.find soinfo v with
                  Not_found ->
                     raise (RefineError ("Itt_hoas_sequent_proof.build_so_witness", StringVarError ("unknown second-order variable", v)))
            in

            (* Construct the context *)
            let vars, hyps = build_bind_context cinfo cvars arity in

            (* The conclusion is the sovar *)
            let t = mk_so_var_term v cvars vars in

            (* Now build the witness term *)
            let seq =
               { sequent_args = vbind_arg_term;
                 sequent_hyps = SeqHyp.of_list hyps;
                 sequent_concl = t
               }
            in
            let t = mk_sequent_term seq in
               t :: witness, succ index) ([], 0) sindex
   in
      mk_list_of_list (List.rev witness)

(*
 * Build the second-order witness.
 *)
let build_context_witness cinfo cindex =
   let witness, _ =
      IntTable.fold (fun (witness, index) index' v ->
            if index' <> index then
               raise (RefineError ("Itt_hoas_sequent_proof.build_context_witness", StringIntError ("witness ordering error", index')));

            (* Info for the var *)
            let cvars, arity =
               try SymbolTable.find cinfo v with
                  Not_found ->
                     raise (RefineError ("Itt_hoas_sequent_proof.build_context_witness", StringVarError ("unknown second-order variable", v)))
            in

            (* Construct the context *)
            let vars, hyps = build_bind_context cinfo cvars arity in

            (* The conclusion is the sovar *)
            let t = mk_hyplist_term v cvars vars in

            (* Now build the witness term *)
            let seq =
               { sequent_args = hyp_context_arg_term;
                 sequent_hyps = SeqHyp.of_list (List.rev hyps);
                 sequent_concl = t
               }
            in
            let t = mk_sequent_term seq in
               t :: witness, succ index) ([], 0) cindex
   in
      mk_list_of_list (List.rev witness)

(*
 * Build the entire witness term.
 *)
let build_proof_witness_term p =
   let t = concl p in
   let cinfo, soinfo = socvars_info (SymbolTable.empty, SymbolTable.empty) t in
   let cindex, soindex = find_var_index IntTable.empty IntTable.empty t in
   let cvars = build_context_witness cinfo cindex in
   let sovars = build_so_witness cinfo soinfo soindex in
      mk_proof_step_witness_term sovars cvars

(*
 * Unify the terms, then instantiate the existential.
 *)
let dest_proof_step_witness p =
   let witness = build_proof_witness_term p in
      exists_intro witness

let proofStepWitnessT = funT dest_proof_step_witness

(*
 * When applying the @tt[provable_intro] get the premises from
 * the assumptions.
 *)
let provable_hyps hyps =
   let hyps =
      SeqHyp.fold (fun hyps _ h ->
            match h with
               Hypothesis (_, t) ->
                  if is_provable_sequent_term t then
                     let _, t = dest_provable_sequent_term t in
                        t :: hyps
                  else
                     hyps
             | Context _ ->
                  hyps) [] hyps
   in
      List.rev hyps

let provable_intro_tac p =
   let hyps = provable_hyps (explode_sequent (Sequent.goal p)).sequent_hyps in
   let hyps_list = mk_list_of_list hyps in
      provable_intro hyps_list

let provableIntroT = funT provable_intro_tac

(************************************************************************
 * The final tactic.
 *)

(*
 * Bring in all the assums.
 *)
let rec assum_all i len =
   if i > len then
      idT
   else
      assumT i thenT assum_all (succ i) len

let assumAllT =
   funT (fun p -> assum_all 1 (Sequent.num_assums p))

let provableRuleStartT t unfold =
   assumAllT
   thenT rwhAll reduce_bsequent
   thenMT forwardChainT
   thenT thinDupT
   thenMT provableIntroT
   thenMT simple_step_intro t
   thenMT rw (higherC unfold thenC reduceC) 0

let provableRuleT t unfold =
   provableRuleStartT t unfold
   thenMT proofStepWitnessT
   thenT proofRuleWFT

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
