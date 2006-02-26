doc <:doc<
   Native sequent representation.  This representation of sequents
   is not a BTerm itself.  If you want to work in a theory where
   sequents are not part of your language, then you should probably
   use this representation, because it is easier to use.

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2005-2006 Mojave Group, Caltech

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
extends Itt_tunion
extends Itt_match
extends Itt_list_set
extends Itt_hoas_util

doc docoff

open Basic_tactics

open Itt_list
open Itt_list2
open Itt_dfun
open Itt_sqsimple
open Itt_struct

doc <:doc<
   A proof step << ProofStep >> represents one rule application
   in a proof.  The proof step has a list of premises, and a goal.
>>
define const unfold_ProofStep : ProofStep <-->
   list{BTerm} * BTerm

define unfold_proof_step : proof_step{'premises; 'goal} <-->
   'premises, 'goal

doc <:doc<
   A << ProofStepWitness >> is an additional argument to a proof checker
   that allows it to check that an inference is valid.  We define a
   single type for all witnesses, including values for the second-order
   and context-variables.
>>
define const unfold_ProofStepWitness : ProofStepWitness <-->
   list{BTerm} * list{list{BTerm}}

define unfold_proof_step_witness : proof_step_witness{'sovars; 'cvars} <-->
   'sovars, 'cvars

doc <:doc<
   The term << ProofRule >> represents a proof checker for
   a single proof step.  Proof checking is always decidable.
>>
define const unfold_ProofRule : ProofRule <-->
   ProofStep * ProofStepWitness -> bool

doc <:doc<
   The term << Logic >> represents a set of proof rules.
>>
define const unfold_Logic : Logic <-->
   list{ProofRule}

doc <:doc<
   A derivation has three parts, 1) the premises << derivation_premises{'d} >>,
   the goal << derivation_goal{'d} >>, and the justification.
>>
define unfold_derivation_premises : derivation_premises{'d} <-->
   fst{'d}

define unfold_derivation_goal : derivation_goal{'d} <-->
   fst{snd{'d}}

doc <:doc<
   The term << ValidStep{'premises; 'goal; 'witness; 'logic} >> is the predicate that determines
   if the proof step matches one of the proof rules in the logic.
>>
define unfold_SimpleStep : SimpleStep{'premises; 'goal; 'witness; 'logic} <-->
   exists_list{'logic; check. "assert"{'check (proof_step{'premises; 'goal}, 'witness)}}
   and 'premises in list{BTerm} and 'goal in BTerm and 'witness in ProofStepWitness and 'logic in Logic

define unfold_ValidStep : ValidStep{'premises; 'goal; 'witness; 'logic} <-->
   exists_list{'logic; check. "assert"{'check (proof_step{map{x. derivation_goal{'x}; 'premises}; 'goal}, 'witness)}}

doc <:doc<
   A << derivation_step{'premises; 'goal; 'witness; 'p} >> forms one step of a derivation,
   where << 'p >> is the proof that the << 'goal >> follows from the << 'premises >>.
>>
define unfold_derivation_step : derivation_step{'premises; 'goal; 'witness; 'p} <-->
   pair{'premises; pair{'goal; pair{'witness; 'p}}}

doc <:doc<
   The term << Derivation{'logic} >> represents the set of
   valid derivations in the logic.  We define it as the finite unrollings of
   proof trees.
>>
define unfold_Derivation_indexed : Derivation{'n; 'logic} <-->
   ind{'n; void; m, T. premises: list{'T} * goal: BTerm * witness: ProofStepWitness * ValidStep{'premises; 'goal; 'witness; 'logic}}

define unfold_Derivation : Derivation{'logic} <-->
   tunion{nat; n. Derivation{'n; 'logic}}
doc docoff

let fold_Logic = makeFoldC << Logic >> unfold_Logic
let fold_derivation_step = makeFoldC << derivation_step{'premises; 'goal; 'witness; 'proof} >> unfold_derivation_step
let fold_proof_step = makeFoldC << proof_step{'premises; 'goal} >> unfold_proof_step
let fold_Derivation_indexed = makeFoldC << Derivation{'n; 'logic} >> unfold_Derivation_indexed
let fold_proof_step_witness = makeFoldC << proof_step_witness{'sovars; 'cvars} >> unfold_proof_step_witness

(*
 * Some reductions.
 *)
interactive_rw reduce_derivation_premises {| reduce |} :
   derivation_premises{derivation_step{'premises; 'goal; 'witness; 'p}}
   <-->
   'premises

interactive_rw reduce_derivation_goal {| reduce |} :
   derivation_goal{derivation_step{'premises; 'goal; 'witness; 'p}}
   <-->
   'goal

(*
 * A proof step properties.
 *)
interactive proof_step_wf {| intro [] |} : <:xrule<
   <H> >- ProofStep Type
>>

interactive proof_step_wf2 {| intro [] |} : <:xrule<
   "wf" : <H> >- premises in list{BTerm} -->
   "wf" : <H> >- goal in BTerm -->
   <H> >- proof_step{premises; goal} IN ProofStep
>>

interactive proof_step_elim {| elim [ThinFirst thinT] |} 'H : <:xrule<
   "wf" : <H>; premises: list{BTerm}; goal: BTerm; <J[proof_step{premises; goal}]> >- C[proof_step{premises; goal}] -->
   <H>; s: ProofStep; <J[s]> >- C[s]
>>

interactive proof_step_sqsimple {| intro []; sqsimple |} : <:xrule<
   <H> >- sqsimple{ProofStep}
>>

(*
 * The ProofStepWitness is a type.
 *)
interactive proof_step_witness_wf {| intro [] |} : <:xrule<
   <H> >- "ProofStepWitness" Type
>>

interactive proof_step_witness_wf2 {| intro [] |} : <:xrule<
   "wf" : <H> >- sovars in list{BTerm} -->
   "wf" : <H> >- cvars in list{list{BTerm}} -->
   <H> >- proof_step_witness{sovars; cvars} in ProofStepWitness
>>

interactive proof_step_witness_elim {| elim [ThinFirst thinT] |} 'H : <:xrule<
   <H>; sovars: list{"BTerm"}; cvars: list{list{"BTerm"}}; <J[proof_step_witness{sovars; cvars}]> >- C[proof_step_witness{sovars; cvars}] -->
   <H>; x: "ProofStepWitness"; <J[x]> >- C[x]
>>

(*
 * A ProofRule is a type for any type.
 *)
interactive proof_rule_wf {| intro [] |} : <:xrule<
   <H> >- ProofRule Type
>>

interactive logic_wf {| intro [] |} : <:xrule<
   <H> >- Logic Type
>>

(*
 * A ValidStep requires a derivation and a goal.
 *)
interactive derivation_premises_wf1 : <:xrule<
   "wf" : <H> >- t IN ty_premises * "top" * "top" -->
   <H> >- derivation_premises{t} IN ty_premises
>>

interactive derivation_goal_wf1 : <:xrule<
   "wf" : <H> >- t IN "top" * BTerm * "top" -->
   <H> >- derivation_goal{t} IN BTerm
>>

interactive valid_step_wf {| intro [intro_typeinf << 'goal >>] |} : <:xrule<
   "wf" : <H> >- premises IN list{"top" * BTerm * "top"} -->
   "wf" : <H> >- goal in BTerm -->
   "wf" : <H> >- witness in "ProofStepWitness" -->
   "wf" : <H> >- logic IN Logic -->
   <H> >- ValidStep{premises; goal; witness; logic} Type
>>

(*
 * The step discards some of the information.
 *)
interactive_rw reduce_derivation_indexed_base {| reduce |} : <:xrewrite<
   Derivation{0; logic}
   <-->
   "void"
>>

interactive_rw reduce_derivation_indexed_step {| reduce |} : <:xrewrite<
   n IN "nat" -->
   Derivation{n +@ 1; logic}
   <-->
   Prod premises: list{Derivation{n; logic}}
   * Prod goal: BTerm
   * Prod witness: "ProofStepWitness"
   * ValidStep{premises; goal; witness; logic}
>>

interactive derivation_indexed_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- logic in Logic -->
   <H> >- Derivation{n; logic} Type
>>

interactive derivation_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- logic in Logic -->
   <H> >- "Derivation"{logic} Type
>>

(*
 * Derivations contain valid steps.
 *)
interactive valid_step_wf2 {| intro [intro_typeinf << 'premises >>] |} list{Derivation{'n; 'logic}} : <:xrule<
   "wf" : <H> >- n IN "nat" -->
   "wf" : <H> >- premises IN list{Derivation{n; logic}} -->
   "wf" : <H> >- goal IN BTerm -->
   "wf" : <H> >- witness IN "ProofStepWitness" -->
   "wf" : <H> >- logic IN Logic -->
   <H> >- ValidStep{premises; goal; witness; logic} Type
>>

(*
 * The type of derivations is monotone.
 *)
interactive derivation_indexed_monotone 'i : <:xrule<
   "wf" : <H> >- logic IN Logic -->
   "wf" : <H> >- i IN "nat" -->
   "wf" : <H> >- j IN "nat" -->
   "aux" : <H> >- i <= j -->
   <H> >- e IN Derivation{i; logic} -->
   <H> >- e IN Derivation{j; logic}
>>

interactive derivation_indexed_list_monotone 'i : <:xrule<
   "wf" : <H> >- logic IN Logic -->
   "wf" : <H> >- i IN "nat" -->
   "wf" : <H> >- j IN "nat" -->
   "aux" : <H> >- i <= j -->
   <H> >- e IN list{Derivation{i; logic}} -->
   <H> >- e IN list{Derivation{j; logic}}
>>

(*
 * The depth of a derivation is computable.
 *)
define unfold_derivation_depth : derivation_depth{'d} <--> <:xterm<
   (fix depth d ->
       list_max{map{premise. depth premise; derivation_premises{d}}} +@ 1) d
>>

let fold_derivation_depth = makeFoldC << derivation_depth{'d} >> unfold_derivation_depth

interactive_rw reduce_derivation_depth {| reduce |} : <:xrewrite<
    derivation_depth{(premises, goal, witness, p)}
    <-->
    list_max{map{premise. derivation_depth{premise}; premises}} +@ 1
>>

interactive derivation_depth_wf1 {| intro [intro_typeinf << 'd >>] |} Derivation{'n; 'ty_logic} : <:xrule<
   "wf" : <H> >- n IN "nat" -->
   "wf" : <H> >- ty_logic IN Logic -->
   "wf" : <H> >- d IN Derivation{n; ty_logic} -->
   <H> >- derivation_depth{d} IN "nat"
>>

interactive derivation_depth_wf {| intro [intro_typeinf << 'd >>] |} Derivation{'ty_logic} : <:xrule<
   "wf" : <H> >- ty_logic IN Logic -->
   "wf" : <H> >- d IN Derivation{ty_logic} -->
   <H> >- derivation_depth{d} IN "nat"
>>

interactive derivation_depth_elim {| elim [ThinFirst thinT] |} 'H : <:xrule<
   "wf" : <H>; e: Derivation{logic}; <J[e]> >- logic IN Logic -->
   <H>; e: Derivation{logic}; <J[e]>; e IN Derivation{derivation_depth{e}; logic} >- C[e] -->
   <H>; e: Derivation{logic}; <J[e]> >- C[e]
>>

interactive derivation_depth_bound {| intro [intro_typeinf << 'e >>] |} Derivation{'n; 'logic} : <:xrule<
   "wf" : <H> >- n IN "nat" -->
   "wf" : <H> >- logic IN Logic -->
   "wf" : <H> >- e IN Derivation{n; logic} -->
   <H> >- derivation_depth{e} <= n
>>

interactive derivation_depth_elim2 'H : <:xrule<
   "wf" : <H>; e: Derivation{n; logic}; <J[e]> >- n IN "nat" -->
   "wf" : <H>; e: Derivation{n; logic}; <J[e]> >- logic IN Logic -->
   <H>; e: Derivation{logic}; <J[e]> >- C[e] -->
   <H>; e: Derivation{n; logic}; <J[e]> >- C[e]
>>

interactive derivation_depth_list_elim2 'H : <:xrule<
   "wf" : <H>; e: list{Derivation{n; logic}}; <J[e]> >- n IN "nat" -->
   "wf" : <H>; e: list{Derivation{n; logic}}; <J[e]> >- logic IN Logic -->
   <H>; e: list{Derivation{logic}}; <J[e]> >- C[e] -->
   <H>; e: list{Derivation{n; logic}}; <J[e]> >- C[e]
>>

doc <:doc<
   This is the general proof induction principle.
>>
interactive derivation_elim {| elim [] |} 'H : <:xrule<
   "wf" : <H>; e: Derivation{logic}; <J[e]> >- logic IN Logic -->
   <H>; e: Derivation{logic}; <J[e]>;
       premises: list{Derivation{logic}};
       goal: BTerm;
       witness: "ProofStepWitness";
       all_list{premises; premise. P[premise]};
       p: ValidStep{premises; goal; witness; logic} >- P[derivation_step{premises; goal; witness; p}] -->
   <H>; e: Derivation{logic}; <J[e]> >- P[e]
>>

doc docoff

(*
 * Restate some of the well-formedness goals.
 *)
interactive derivation_goal_wf2 {| intro [intro_typeinf << 'e >>] |} Derivation{'logic} : <:xrule<
   "wf" : <H> >- logic IN "Logic" -->
   "wf" : <H> >- e IN Derivation{logic} -->
   <H> >- derivation_goal{e} in BTerm
>>

interactive valid_step_wf3 {| intro [intro_typeinf << 'premises >>] |} list{Derivation{'logic}} : <:xrule<
   "wf" : <H> >- premises in list{Derivation{logic}} -->
   "wf" : <H> >- goal in BTerm -->
   "wf" : <H> >- witness in ProofStepWitness -->
   "wf" : <H> >- logic in Logic -->
   <H> >- ValidStep{premises; goal; witness; logic} Type
>>

doc <:doc<
   The << Provable{'logic; 't} >> predicate specifies that a particular
   term << 't >> is the root of a derivation in a logic.
>>
define unfold_Provable : Provable{'logic; 't} <-->
   exst e: Derivation{'logic}.
      derivation_goal{'e} = 't in BTerm
doc docoff

interactive wf_Provable {| intro [] |} : <:xrule<
    "wf" : <H> >- logic IN Logic -->
    "wf" : <H> >- t IN BTerm -->
    <H> >- Provable{logic; t} Type
>>

doc <:doc<
   Introduction forms.
>>
interactive derivation_step_intro {| intro [] |} : <:xrule<
   "wf" : <H> >- logic in Logic -->
   "wf" : <H> >- premises in list{Derivation{logic}} -->
   "wf" : <H> >- goal in BTerm -->
   "wf" : <H> >- witness in ProofStepWitness -->
   "wf" : <H> >- p in ValidStep{premises; goal; witness; logic} -->
   <H> >- derivation_step{premises; goal; witness; p} in Derivation{logic}
>>

(************************************************************************
 * Alpha-equality.
 *)
doc <:doc<
   Define alpha-equality on proof steps.
>>
define unfold_beq_proof_step : beq_proof_step{'step1; 'step2} <--> <:xterm<
   let premises1, goal1 = step1 in
   let premises2, goal2 = step2 in
      beq_bterm_list{premises1; premises2} &&b beq_bterm{goal1; goal2}
>>

interactive_rw reduce_beq_proof_step {| reduce |} : <:xrewrite<
   beq_proof_step{proof_step{premises1; goal1}; proof_step{premises2; goal2}}
   <-->
   beq_bterm_list{premises1; premises2} &&b beq_bterm{goal1; goal2}
>>

interactive beq_proof_step_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- step1 in ProofStep -->
   "wf" : <H> >- step2 IN ProofStep -->
   <H> >- beq_proof_step{step1; step2} in bool
>>

interactive beq_proof_step_intro {| intro [] |} : <:xrule<
   <H> >- s1 = s2 in ProofStep -->
   <H> >- "assert"{beq_proof_step{s1; s2}}
>>

interactive beq_proof_step_elim {| elim [] |} 'H : <:xrule<
   "wf" : <H>; u: "assert"{beq_proof_step{s1; s2}}; <J[u]> >- s1 in ProofStep -->
   "wf" : <H>; u: "assert"{beq_proof_step{s1; s2}}; <J[u]> >- s2 in ProofStep -->
   <H>; u: s1 = s2 in ProofStep; <J[u]> >- C[u] -->
   <H>; u: "assert"{beq_proof_step{s1; s2}}; <J[u]> >- C[u]
>>

(************************************************************************
 * Logic operations.
 *)
define unfold_empty_logic : empty_logic <-->
   nil

define unfold_rules_logic : rules_logic{'rules; 'logic} <-->
   append{'rules; 'logic}

define unfold_union_logic : union_logic{'logic1; 'logic2} <-->
   append{'logic1; 'logic2}

define unfold_MemLogic : MemLogic{'step; 'logic} <--> <:xterm<
   mem{step; logic; ProofRule}
>>

define unfold_SubLogic : SubLogic{'logic1; 'logic2} <--> <:xterm<
   "subset"{logic1; logic2; ProofRule}
>>

interactive nil_logic_wf {| intro [] |} : <:xrule<
   <H> >- empty_logic{} in Logic
>>

interactive rules_logic_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- rules in list{ProofRule} -->
   "wf" : <H> >- logic in Logic -->
   <H> >- rules_logic{rules; logic} in Logic
>>

interactive union_logic_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- logic1 in Logic -->
   "wf" : <H> >- logic2 in Logic -->
   <H> >- union_logic{logic1; logic2} in Logic
>>

interactive mem_logic_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- step in ProofRule -->
   "wf" : <H> >- logic in Logic -->
   <H> >- MemLogic{step; logic} Type
>>

interactive sub_logic_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- logic1 in Logic -->
   "wf" : <H> >- logic2 in Logic -->
   <H> >- SubLogic{logic1; logic2} Type
>>

(*
 * Membership in a logic.
 *)
interactive mem_logic_trans 'logic1 : <:xrule<
   "wf" : <H> >- logic1 in Logic -->
   "wf" : <H> >- logic2 in Logic -->
   "wf" : <H> >- step in ProofRule -->
   <H> >- SubLogic{logic1; logic2} -->
   <H> >- MemLogic{step; logic1} -->
   <H> >- MemLogic{step; logic2}
>>

interactive mem_rules_logic {| intro [] |} : <:xrule<
   "wf" : <H> >- step in ProofRule -->
   "wf" : <H> >- logic in Logic -->
   "wf" : <H> >- steps in list{ProofRule} -->
   "wf" : <H> >- mem{step; steps; ProofRule} -->
   <H> >- MemLogic{step; rules_logic{steps; logic}}
>>

interactive mem_union_logic1 {| intro [SelectOption 1] |} : <:xrule<
   "wf" : <H> >- step in ProofRule -->
   "wf" : <H> >- logic1 in Logic -->
   "wf" : <H> >- logic2 in Logic -->
   <H> >- MemLogic{step; logic1} -->
   <H> >- MemLogic{step; union_logic{logic1; logic2}}
>>

interactive mem_union_logic2 {| intro [SelectOption 2] |} : <:xrule<
   "wf" : <H> >- step in ProofRule -->
   "wf" : <H> >- logic1 in Logic -->
   "wf" : <H> >- logic2 in Logic -->
   <H> >- MemLogic{step; logic2} -->
   <H> >- MemLogic{step; union_logic{logic1; logic2}}
>>

(************************************************************************
 * Additional wf rules.
 *)
interactive proof_rule_start_wf {| intro [] |} : <:xrule<
   "wf" : <H>; s: ProofStep; w: ProofStepWitness >- e[s; w] in "bool" -->
   <H> >- lambda{step. spread{step; s, w. e[s; w]}} in ProofRule
>>

interactive simple_step_wf {| intro [intro_typeinf << 'goal >>] |} : <:xrule<
   "wf" : <H> >- premises in list{BTerm} -->
   "wf" : <H> >- goal in BTerm -->
   "wf" : <H> >- witness in ProofStepWitness -->
   "wf" : <H> >- logic in Logic -->
   <H> >- SimpleStep{premises; goal; witness; logic} Type
>>

(************************************************************************
 * Tactics.
 *)
let proof_step_witness_term = << proof_step_witness{'sovars; 'cvars} >>
let proof_step_witness_opname = opname_of_term proof_step_witness_term
let is_proof_step_witness_term = is_dep0_dep0_term proof_step_witness_opname
let mk_proof_step_witness_term = mk_dep0_dep0_term proof_step_witness_opname
let dest_proof_step_witness_term = dest_dep0_dep0_term proof_step_witness_opname

let beq_proof_step_term = << beq_proof_step{'step1; 'step2} >>
let beq_proof_step_opname = opname_of_term beq_proof_step_term
let is_beq_proof_step_term = is_dep0_dep0_term beq_proof_step_opname
let dest_beq_proof_step_term = dest_dep0_dep0_term beq_proof_step_opname

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
