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
open Itt_dprod
open Itt_logic
open Itt_int_base
open Itt_hoas_base
open Itt_hoas_vbind
open Itt_hoas_vector
open Itt_hoas_proof
open Itt_hoas_sequent
open Itt_hoas_sequent_term
open Itt_hoas_sequent_proof_step

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
   <H> >- all_list{premises; premise. Provable{logic; premise}} -->
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
 * Tactics.
 *)
doc docoff

let provable_sequent_term = << Provable{'logic; 'seq} >>
let provable_sequent_opname = opname_of_term provable_sequent_term
let is_provable_sequent_term = is_dep0_dep0_term provable_sequent_opname

(*
 * Substitutions for sloppy unification.
 *)
type subst =
   { subst_sovars : var IntTable.t;
     subst_cvars  : var IntTable.t;
     subst_vars   : term SymbolTable.t
   }

let subst_empty =
   { subst_sovars = IntTable.empty;
     subst_cvars  = IntTable.empty;
     subst_vars   = SymbolTable.empty
   }

let subst_add_sovar subst v i =
   { subst with subst_sovars = IntTable.add subst.subst_sovars i v }

let subst_add_cvar subst v i =
   { subst with subst_cvars = IntTable.add subst.subst_cvars i v }

let subst_add_var subst v t =
   { subst with subst_vars = SymbolTable.add subst.subst_vars v t }

(*
 * Construct the witness term from the unification info.
 *)
let witness_of_subst subst =
   let { subst_sovars = sovars;
         subst_cvars  = cvars;
         subst_vars   = vars
       } = subst
   in
   let sovars, _ =
      IntTable.fold (fun (sovars, i) i' v ->
            if i' <> i then
               raise (RefineError ("Itt_hoas_sequent_proof.witness_of_subst", StringIntError ("missing sovar", i)));
            let sovars =
               try SymbolTable.find vars v :: sovars with
                  Not_found ->
                     raise (RefineError ("Itt_hoas_sequent_proof.witness_of_subst", StringVarError ("missing sovar", v)))
            in
               sovars, succ i) ([], 0) sovars
   in
   let cvars, _ =
      IntTable.fold (fun (cvars, i) i' v ->
            if i' <> i then
               raise (RefineError ("Itt_hoas_sequent_proof.witness_of_subst", StringIntError ("missing sovar", i)));
            let cvars =
               try SymbolTable.find vars v :: cvars with
                  Not_found ->
                     raise (RefineError ("Itt_hoas_sequent_proof.witness_of_subst", StringVarError ("missing sovar", v)))
            in
               cvars, succ i) ([], 0) cvars
   in

   (* Build the witness term *)
   let sovars = mk_list_of_list (List.rev sovars) in
   let cvars = mk_list_of_list (List.rev cvars) in
      mk_proof_step_witness_term sovars cvars

(*
 * Sloppy unification.
 *)
let rec unify_term subst t1 t2 =
   if !debug_sequent_proof then
      eprintf "@[<v 3>unify_term:@ %s@ %s@]@." (**)
         (SimplePrint.string_of_term t1)
         (SimplePrint.string_of_term t2);
   if is_hyp_context_term t1 then
      let _, t1 = dest_hyp_context_term t1 in
         unify_term subst t1 t2
   else if is_vbind_term t1 then
      let _, t1 = dest_vbind_term t1 in
         unify_term subst t1 t2
   else if is_bind_term t2 then
      let _, t2 = dest_bind_term t2 in
         unify_term subst t1 t2
   else if is_bindn_term t2 then
      let _, _, t2 = dest_bindn_term t2 in
         unify_term subst t1 t2
   else if is_var_term t2 then
      subst_add_var subst (dest_var t2) t1
   else if is_vsequent_term t1 && is_vsequent_term t2 then
      let _, hyps1, concl1 = dest_vsequent_term t1 in
      let _, hyps2, concl2 = dest_vsequent_term t2 in
      let subst = unify_hyps subst hyps1 hyps2 in
         unify_term subst concl1 concl2
   else
      let { term_op = op1; term_terms = terms1 } = dest_term t1 in
      let { term_op = op2; term_terms = terms2 } = dest_term t2 in
      let { op_name = opname1; op_params = params1 } = dest_op op1 in
      let { op_name = opname2; op_params = params2 } = dest_op op2 in
         if Opname.eq opname1 opname2 then
            let subst = unify_param_list subst params1 params2 in
               unify_bterm_list subst terms1 terms2
         else
            raise (RefineError ("Itt_hoas_sequent_proof.unify_term", StringError "term mismatch"))

and unify_term_list subst tl1 tl2 =
   let len1 = List.length tl1 in
   let len2 = List.length tl2 in
      if len1 = len2 then
         List.fold_left2 unify_term subst tl1 tl2
      else
         raise (RefineError ("Itt_hoas_sequent_proof.unify_term_list", StringError "arity mismatch"))

and unify_param subst p1 p2 =
   let eq =
      match dest_param p1, dest_param p2 with
         Number n1, Number n2 ->
            Lm_num.eq_num n1 n2
       | String s1, String s2 ->
            s1 = s2
       | Token t1, Token t2 ->
            Opname.eq t1 t2
       | Var v1, Var v2 ->
            Lm_symbol.eq v1 v2
       | Shape s1, Shape s2 ->
            TermShape.shape_eq s1 s2
       | Operator o1, Operator o2 ->
            opparam_eq o1 o2
       | Quote, Quote ->
            true
       | _ ->
            false
   in
      if eq then
         subst
      else
         raise (RefineError ("Itt_hoas_sequent_proof.unify_param", (**)
                                StringErrorError ("parameter mismatch",
                                ParamErrorError (p1, ParamError p2))))

and unify_param_list subst pl1 pl2 =
   let len1 = List.length pl1 in
   let len2 = List.length pl2 in
      if len1 = len2 then
         List.fold_left2 unify_param subst pl1 pl2
      else
         raise (RefineError ("Itt_hoas_sequent_proof.unify_param_list", (**)
                                StringErrorError ("arity mismatch",
                                IntErrorError (len1, IntError len2))))

and unify_bterm subst bt1 bt2 =
   let { bvars = vars1; bterm = t1 } = dest_bterm bt1 in
   let { bvars = vars2; bterm = t2 } = dest_bterm bt2 in
   let len1 = List.length vars1 in
   let len2 = List.length vars2 in
      if len1 = len2 then
         unify_term subst t1 t2
      else
         raise (RefineError ("Itt_hoas_sequent_proof.unify_bterm", (**)
                                StringErrorError ("arity mismatch",
                                IntErrorError (len1, IntError len2))))

and unify_bterm_list subst btl1 btl2 =
   let len1 = List.length btl1 in
   let len2 = List.length btl2 in
      if len1 = len2 then
         List.fold_left2 unify_bterm subst btl1 btl2
      else
         raise (RefineError ("Itt_hoas_sequent_proof.unify_bterm_list", (**)
                                StringErrorError ("arity mismatch",
                                IntErrorError (len1, IntError len2))))

and unify_hyps subst hyps1 hyps2 =
   let len1 = SeqHyp.length hyps1 in
   let len2 = SeqHyp.length hyps2 in
   let () =
      if len1 <> len2 then
         raise (RefineError ("Itt_hoas_sequent_proof.unify_hyps", (**)
                                StringErrorError ("arity mismatch",
                                IntErrorError (len1, IntError len2))))
   in
   let rec unify subst i =
      if i = len1 then
         subst
      else
         match SeqHyp.get hyps1 i, SeqHyp.get hyps2 i with
            Hypothesis (_, t1), Hypothesis (_, t2) ->
               let subst = unify_term subst t1 t2 in
                  unify subst (succ i)
          | _ ->
               raise (RefineError ("Itt_hoas_sequent_proof.unify_hyps", StringError "illegal context"))
   in
      unify subst 0

let rec unify_start subst t =
   if is_exists_term t then
      let _, _, t = dest_exists t in
         unify_start subst t
   else if is_assert_term t then
      unify_start subst (dest_assert t)
   else if is_let_cvar_term t then
      let _, _, i, v, t = dest_let_cvar_term t in
      let i = int_of_num (dest_number i) in
      let subst = subst_add_cvar subst v i in
         unify_start subst t
   else if is_let_sovar_term t then
      let _, _, i, v, t = dest_let_sovar_term t in
      let i = int_of_num (dest_number i) in
      let subst = subst_add_sovar subst v i in
         unify_start subst t
   else if is_beq_sequent_term t then
      let t1, t2 = dest_beq_sequent_term t in
         unify_term subst t1 t2
   else
      raise (RefineError ("Itt_hoas_sequent_proof.unify_start", StringTermError ("unexpected term", t)))

(*
 * Unify the terms, then instantiate the existential.
 *)
let dest_proof_step_witness p =
   let subst = unify_start subst_empty (concl p) in
   let witness = witness_of_subst subst in
      exists_intro witness

let proofStepWitnessT = funT dest_proof_step_witness

(*
 * When applying the @tt[provable_intro] get the premises from
 * the assumptions.
 *)
let provable_premises assums =
   let premises =
      List.fold_left (fun premises assum ->
            let concl = (explode_sequent assum).sequent_concl in
               if is_provable_sequent_term concl then
                  concl :: premises
               else
                  premises) [] assums
   in
      List.rev premises

let provable_intro_tac p =
   let premises = provable_premises (all_assums p) in
   let premises_list = mk_list_of_list premises in
      provable_intro premises_list

let provableIntroT = funT provable_intro_tac

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
