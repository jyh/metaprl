doc <:doc<
   Native sequent representation.  This representation of sequents
   is not a BTerm itself.  If you want to work in a theory where
   sequents are not part of your language, then you should probably
   use this representation, because it is easier to use.

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
extends Itt_tunion
extends Itt_match
extends Itt_hoas_util

doc docoff

open Dform
open Basic_tactics

open Itt_list
open Itt_list2
open Itt_dfun

doc <:doc<
   A proof step << ProofStep{'ty_sequent} >> represents one rule application
   in a proof.  The proof step has a list of premises, and a goal.
>>
define unfold_ProofStep : ProofStep{'ty_sequent} <-->
   list{'ty_sequent} * 'ty_sequent

define unfold_proof_step : proof_step{'premises; 'goal} <-->
   'premises, 'goal

doc <:doc<
   A << ProofStepWitness >> is an additional argument to a proof checker
   that allows it to check that an inference is valid.  We define a
   single type for all witnesses, including values for the second-order
   and context-variables.
>>
define unfold_ProofStepWitness : ProofStepWitness <-->
   list{BTerm} * list{list{BTerm}}

define unfold_proof_step_witness : proof_step_witness{'sovars; 'cvars} <-->
   'sovars, 'cvars

doc <:doc<
   The term << ProofRule{'ty_sequent} >> represents a proof checker for
   a single proof step.  Proof checking is always decidable.
>>
define unfold_ProofRule : ProofRule{'ty_sequent} <-->
   ProofStep{'ty_sequent} * ProofStepWitness -> bool

doc <:doc<
   The term << Logic{'ty_sequent} >> represents a set of proof rules.
>>
define unfold_Logic : Logic{'ty_sequent} <-->
   list{ProofRule{'ty_sequent}}

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
define unfold_ValidStep : ValidStep{'premises; 'goal; 'witness; 'logic} <-->
   exists_list{'logic; check. "assert"{'check (proof_step{map{x. derivation_goal{'x}; 'premises}; 'goal}, 'witness)}}

doc <:doc<
   A << derivation_step{'premises; 'goal; 'witness; 'p} >> forms one step of a derivation,
   where << 'p >> is the proof that the << 'goal >> follows from the << 'premises >>.
>>
define unfold_derivation_step : derivation_step{'premises; 'goal; 'witness; 'p} <-->
   pair{'premises; pair{'goal; pair{'witness; 'p}}}

doc <:doc<
   The term << Derivation{'ty_sequent; 'logic} >> represents the set of
   valid derivations in the logic.  We define it as the finite unrollings of
   proof trees.
>>
define unfold_Derivation_indexed : Derivation{'n; 'ty_sequent; 'logic} <-->
   ind{'n; void; m, T. premises: list{'T} * goal: 'ty_sequent * witness: ProofStepWitness * ValidStep{'premises; 'goal; 'witness; 'logic}}

define unfold_Derivation : Derivation{'ty_sequent; 'logic} <-->
   tunion{nat; n. Derivation{'n; 'ty_sequent; 'logic}}
doc docoff

let fold_Logic = makeFoldC << Logic{'ty_sequent} >> unfold_Logic
let fold_derivation_step = makeFoldC << derivation_step{'premises; 'goal; 'witness; 'proof} >> unfold_derivation_step
let fold_proof_step = makeFoldC << proof_step{'premises; 'goal} >> unfold_proof_step
let fold_Derivation_indexed = makeFoldC << Derivation{'n; 'ty_sequent; 'logic} >> unfold_Derivation_indexed
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
 * A proof step can range over any type.
 *)
interactive proof_step_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- ty Type -->
   <H> >- ProofStep{ty} Type
>>

interactive proof_step_wf2 {| intro [] |} : <:xrule<
   "wf" : <H> >- premises IN list{ty} -->
   "wf" : <H> >- goal IN ty -->
   <H> >- proof_step{premises; goal} IN ProofStep{ty}
>>

interactive proof_step_elim {| elim [] |} 'H : <:xrule<
   "wf" : <H>; premises: list{ty}; goal: ty; <J[proof_step{premises; goal}]> >- C[proof_step{premises; goal}] -->
   <H>; s: ProofStep{ty}; <J[s]> >- C[s]
>>

(*
 * The ProofStepWitness is a type.
 *)
interactive proof_step_witness_wf {| intro [] |} : <:xrule<
   <H> >- "ProofStepWitness" Type
>>

interactive proof_step_witness_wf2 {| intro [] |} : <:xrule<
   "wf" : <H> >- sovars IN list{"BTerm"} -->
   "wf" : <H> >- cvars IN list{list{"BTerm"}} -->
   <H> >- proof_step_witness{sovars; cvars} IN "ProofStepWitness"
>>

interactive proof_step_witness_elim {| elim [] |} 'H : <:xrule<
   <H>; sovars: list{"BTerm"}; cvars: list{list{"BTerm"}}; <J[proof_step_witness{sovars; cvars}]> >- C[proof_step_witness{sovars; cvars}] -->
   <H>; x: "ProofStepWitness"; <J[x]> >- C[x]
>>

(*
 * A ProofRule is a type for any type.
 *)
interactive proof_rule_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- ty Type -->
   <H> >- ProofRule{ty} Type
>>

interactive logic_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- ty Type -->
   <H> >- "Logic"{ty} Type
>>

(*
 * A ValidStep requires a derivation and a goal.
 *)
interactive derivation_premises_wf1 : <:xrule<
   "wf" : <H> >- t IN ty_premises * "top" * "top" -->
   <H> >- derivation_premises{t} IN ty_premises
>>

interactive derivation_goal_wf1 : <:xrule<
   "wf" : <H> >- t IN "top" * ty_sequent * "top" -->
   <H> >- derivation_goal{t} IN ty_sequent
>>

interactive valid_step_wf {| intro [intro_typeinf << 'goal >>] |} 'ty_sequent : <:xrule<
   "wf" : <H> >- ty_sequent Type -->
   "wf" : <H> >- premises IN list{"top" * ty_sequent * "top"} -->
   "wf" : <H> >- goal IN ty_sequent -->
   "wf" : <H> >- witness IN "ProofStepWitness" -->
   "wf" : <H> >- logic IN Logic{ty_sequent} -->
   <H> >- ValidStep{premises; goal; witness; logic} Type
>>

(*
 * The step discards some of the information.
 *)
interactive_rw reduce_derivation_indexed_base {| reduce |} : <:xrewrite<
   Derivation{0; ty_sequent; logic}
   <-->
   "void"
>>

interactive_rw reduce_derivation_indexed_step {| reduce |} : <:xrewrite<
   n IN "nat" -->
   Derivation{n +@ 1; ty_sequent; logic}
   <-->
   Prod premises: list{Derivation{n; ty_sequent; logic}}
   * Prod goal: ty_sequent
   * Prod witness: "ProofStepWitness"
   * ValidStep{premises; goal; witness; logic}
>>

interactive derivation_indexed_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- n IN "nat" -->
   "wf" : <H> >- ty_sequent Type -->
   "wf" : <H> >- logic IN Logic{ty_sequent} -->
   <H> >- Derivation{n; ty_sequent; logic} Type
>>

interactive derivation_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- ty_sequent Type -->
   "wf" : <H> >- logic IN "Logic"{ty_sequent} -->
   <H> >- "Derivation"{ty_sequent; logic} Type
>>

(*
 * Derivations contain valid steps.
 *)
interactive valid_step_wf2 {| intro [intro_typeinf << 'premises >>] |} list{Derivation{'n; 'ty_sequent; 'logic}} : <:xrule<
   "wf" : <H> >- n IN "nat" -->
   "wf" : <H> >- ty_sequent Type -->
   "wf" : <H> >- premises IN list{Derivation{n; ty_sequent; logic}} -->
   "wf" : <H> >- goal IN ty_sequent -->
   "wf" : <H> >- witness IN "ProofStepWitness" -->
   "wf" : <H> >- logic IN Logic{ty_sequent} -->
   <H> >- ValidStep{premises; goal; witness; logic} Type
>>

(*
 * The type of derivations is monotone.
 *)
interactive derivation_indexed_monotone 'i : <:xrule<
   "wf" : <H> >- ty_sequent Type -->
   "wf" : <H> >- logic IN Logic{ty_sequent} -->
   "wf" : <H> >- i IN "nat" -->
   "wf" : <H> >- j IN "nat" -->
   "aux" : <H> >- i <= j -->
   <H> >- e IN Derivation{i; ty_sequent; logic} -->
   <H> >- e IN Derivation{j; ty_sequent; logic}
>>

interactive derivation_indexed_list_monotone 'i : <:xrule<
   "wf" : <H> >- ty_sequent Type -->
   "wf" : <H> >- logic IN Logic{ty_sequent} -->
   "wf" : <H> >- i IN "nat" -->
   "wf" : <H> >- j IN "nat" -->
   "aux" : <H> >- i <= j -->
   <H> >- e IN list{Derivation{i; ty_sequent; logic}} -->
   <H> >- e IN list{Derivation{j; ty_sequent; logic}}
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

interactive derivation_depth_wf1 {| intro [intro_typeinf << 'd >>] |} Derivation{'n; 'ty_sequent; 'ty_logic} : <:xrule<
   "wf" : <H> >- n IN "nat" -->
   "wf" : <H> >- ty_sequent Type -->
   "wf" : <H> >- ty_logic IN Logic{ty_sequent} -->
   "wf" : <H> >- d IN Derivation{n; ty_sequent; ty_logic} -->
   <H> >- derivation_depth{d} IN "nat"
>>

interactive derivation_depth_wf {| intro [intro_typeinf << 'd >>] |} Derivation{'ty_sequent; 'ty_logic} : <:xrule<
   "wf" : <H> >- ty_sequent Type -->
   "wf" : <H> >- ty_logic IN Logic{ty_sequent} -->
   "wf" : <H> >- d IN Derivation{ty_sequent; ty_logic} -->
   <H> >- derivation_depth{d} IN "nat"
>>

interactive derivation_depth_elim {| elim [] |} 'H : <:xrule<
   "wf" : <H>; e: Derivation{ty_sequent; logic}; <J[e]> >- ty_sequent Type -->
   "wf" : <H>; e: Derivation{ty_sequent; logic}; <J[e]> >- logic IN Logic{ty_sequent} -->
   <H>; e: Derivation{ty_sequent; logic}; <J[e]>; e IN Derivation{derivation_depth{e}; ty_sequent; logic} >- C[e] -->
   <H>; e: Derivation{ty_sequent; logic}; <J[e]> >- C[e]
>>

interactive derivation_depth_bound {| intro [intro_typeinf << 'e >>] |} Derivation{'n; 'ty_sequent; 'logic} : <:xrule<
   "wf" : <H> >- n IN "nat" -->
   "wf" : <H> >- ty_sequent Type -->
   "wf" : <H> >- logic IN Logic{ty_sequent} -->
   "wf" : <H> >- e IN Derivation{n; ty_sequent; logic} -->
   <H> >- derivation_depth{e} <= n
>>

interactive derivation_depth_elim2 'H : <:xrule<
   "wf" : <H>; e: Derivation{n; ty_sequent; logic}; <J[e]> >- n IN "nat" -->
   "wf" : <H>; e: Derivation{n; ty_sequent; logic}; <J[e]> >- ty_sequent Type -->
   "wf" : <H>; e: Derivation{n; ty_sequent; logic}; <J[e]> >- logic IN Logic{ty_sequent} -->
   <H>; e: Derivation{ty_sequent; logic}; <J[e]> >- C[e] -->
   <H>; e: Derivation{n; ty_sequent; logic}; <J[e]> >- C[e]
>>

interactive derivation_depth_list_elim2 'H : <:xrule<
   "wf" : <H>; e: list{Derivation{n; ty_sequent; logic}}; <J[e]> >- n IN "nat" -->
   "wf" : <H>; e: list{Derivation{n; ty_sequent; logic}}; <J[e]> >- ty_sequent Type -->
   "wf" : <H>; e: list{Derivation{n; ty_sequent; logic}}; <J[e]> >- logic IN Logic{ty_sequent} -->
   <H>; e: list{Derivation{ty_sequent; logic}}; <J[e]> >- C[e] -->
   <H>; e: list{Derivation{n; ty_sequent; logic}}; <J[e]> >- C[e]
>>

doc <:doc<
   This is the general proof induction principle.
>>
interactive derivation_elim {| elim [] |} 'H : <:xrule<
   "wf" : <H>; e: Derivation{ty_sequent; logic}; <J[e]> >- ty_sequent Type -->
   "wf" : <H>; e: Derivation{ty_sequent; logic}; <J[e]> >- logic IN Logic{ty_sequent} -->
   <H>; e: Derivation{ty_sequent; logic}; <J[e]>;
       premises: list{Derivation{ty_sequent; logic}};
       goal: ty_sequent;
       witness: "ProofStepWitness";
       all_list{premises; premise. P[premise]};
       p: ValidStep{premises; goal; witness; logic} >- P[derivation_step{premises; goal; witness; p}] -->
   <H>; e: Derivation{ty_sequent; logic}; <J[e]> >- P[e]
>>

doc docoff

(*
 * Restate some of the well-formedness goals.
 *)
interactive derivation_goal_wf2 {| intro [intro_typeinf << 'e >>] |} Derivation{'ty_sequent; 'logic} : <:xrule<
   "wf" : <H> >- ty_sequent Type -->
   "wf" : <H> >- logic IN "Logic"{ty_sequent} -->
   "wf" : <H> >- e IN Derivation{ty_sequent; logic} -->
   <H> >- derivation_goal{e} IN ty_sequent
>>

doc <:doc<
   The << Provable{'ty_sequent; 'logic; 't} >> predicate specifies that a particular
   term << 't >> is the root of a derivation in a logic.
>>
define unfold_Provable : Provable{'ty_sequent; 'logic; 't} <-->
   exst e: Derivation{'ty_sequent; 'logic}.
      derivation_goal{'e} = 't in 'ty_sequent
doc docoff

interactive wf_Provable {| intro [] |} : <:xrule<
    "wf" : <H> >- ty_sequent Type -->
    "wf" : <H> >- logic IN Logic{ty_sequent} -->
    "wf" : <H> >- t IN ty_sequent -->
    <H> >- Provable{ty_sequent; logic; t} Type
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

define unfold_SubLogic : SubLogic{'ty; 'logic1; 'logic2} <--> <:xterm<
   "subset"{logic1; logic2; ProofRule{ty}}
>>

interactive nil_logic_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- ty Type -->
   <H> >- empty_logic{} in Logic{ty}
>>

interactive rules_logic_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- rules in list{ProofRule{ty}} -->
   "wf" : <H> >- logic in Logic{ty} -->
   <H> >- rules_logic{rules; logic} in Logic{ty}
>>

interactive union_logic_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- logic1 in Logic{ty} -->
   "wf" : <H> >- logic2 in Logic{ty} -->
   <H> >- union_logic{logic1; logic2} in Logic{ty}
>>

interactive sub_logic_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- logic1 in Logic{ty} -->
   "wf" : <H> >- logic2 in Logic{ty} -->
   <H> >- SubLogic{ty; logic1; logic2} Type
>>

(************************************************************************
 * Additional wf rules.
 *)
interactive proof_rule_start_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- ty Type -->
   "wf" : <H>; s: ProofStep{ty}; w: ProofStepWitness{} >- e[s; w] in "bool" -->
   <H> >- lambda{step. spread{step; s, w. e[s; w]}} in ProofRule{ty}
>>

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
