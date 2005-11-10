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
   A sequent is represented as a 3-tuple << BTerm * list{BTerm} * BTerm >>,
   where the first term is the argument, the second is the hypotheses,
   and the final term is the conclusion.
>>
define unfold_sequent : "sequent"{'arg; 'hyps; 'concl} <-->
   ('arg, ('hyps, 'concl))

doc <:doc<
   A sequent is well-formed only if the hypotheses have depths increasing
   by one, and the conclusion is also at the right nesting depth.

   The << hyp_depths{'d; 'l} >> predicate tests whether the list << 'l >>
   is a valid list of terms with binding depths started with << 'd >>.
>>
define unfold_hyp_depths : hyp_depths{'d; 'l} <-->
   list_ind{'l; lambda{d. "true"}; h, t, g. lambda{d. bdepth{'h} = 'd in nat & 'g ('d +@ 1)}} 'd

doc <:doc<
   The << is_sequent{'s} >> predicate tests whether a sequent << 's >> is well-formed
   with respect to binding depths.
   The argument must have depth << 0 >>, the hypotheses must have binding depths
   starting with << 0 >>, and the conclusion must have binding depth
   << length{'hyps} >>.
>>
define unfold_is_sequent : is_sequent{'s} <-->
   spread{'s; arg, rest. spread{'rest; hyps, concl.
      bdepth{'arg} = 0 in nat
      & hyp_depths{0; 'hyps}
      & bdepth{'concl} = length{'hyps} in nat}}

doc <:doc<
   The term << Sequent >> represents the type of sequents.
>>
define unfold_Sequent : Sequent <-->
   { s: BTerm * list{BTerm} * BTerm | is_sequent{'s} }

doc <:doc<
   The << SOVar{'d} >> term represents a second-order variable
   with binding depth << 'd >>.
>>
define unfold_SOVar : SOVar{'d} <-->
   { e: BTerm | bdepth{'e} = 'd in nat }

doc <:doc<
   The << CVar{'d} >> represents a sequent context at binding depth << 'd >>.
>>
define unfold_CVar : CVar{'d} <-->
   { l: list{BTerm} | hyp_depths{'d; 'l} }

doc docoff

let fold_hyp_depths = makeFoldC << hyp_depths{'d; 'l} >> unfold_hyp_depths
let fold_sequent = makeFoldC << "sequent"{'arg; 'hyps; 'goal} >> unfold_sequent

(*
 * hyp_depths rules.
 *)
interactive hyp_depths_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   "wf" : <H> >- l IN list{"BTerm"} -->
   <H> >- hyp_depths{d; l} Type
>>

(*
 * is_sequent is well-formed if applied to a sequent triple.
 *)
interactive is_sequent_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- s IN "BTerm" * list{"BTerm"} * "BTerm" -->
   <H> >- is_sequent{s} Type
>>

(*
 * This is similar, but we have an explicit sequent triple.
 *)
interactive is_sequent_wf2 {| intro [] |} : <:xrule<
   "wf" : <H> >- arg IN "BTerm" -->
   "wf" : <H> >- hyps IN list{"BTerm"} -->
   "wf" : <H> >- concl IN "BTerm" -->
   <H> >- is_sequent{"sequent"{arg; hyps; concl}} Type
>>

(*
 * The Sequent type is well-formed if all the types are subtypes
 * of BTerm.
 *)
interactive sequent_wf {| intro [] |} : <:xrule<
   <H> >- "Sequent" Type
>>

(*
 * An actual sequent has the sequent type if the types
 * and depths match up.
 *)
interactive sequent_term_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- arg IN "BTerm" -->
   "wf" : <H> >- hyps IN list{"BTerm"} -->
   "wf" : <H> >- concl IN "BTerm" -->
   "wf" : <H> >- bdepth{arg} = 0 in "nat" -->
   "wf" : <H> >- hyp_depths{0; hyps} -->
   "wf" : <H> >- bdepth{concl} = length{hyps} in "nat" -->
   <H> >- "sequent"{arg; hyps; concl} IN "Sequent"
>>

(*
 * Elimination, to the three parts.
 *)
interactive sequent_elim {| elim [] |} 'H : <:xrule<
   <H>; arg: "BTerm"; hyps: list{"BTerm"}; goal: "BTerm"; squash{is_sequent{"sequent"{arg; hyps; goal}}};
      <J["sequent"{arg; hyps; goal}]> >- C["sequent"{arg; hyps; goal}] -->
   <H>; s: "Sequent"; <J[s]> >- C[s]
>>

(*
 * An SOVar is well-formed over subtypes of BTerm.
 *)
interactive sovar_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   <H> >- SOVar{d} Type
>>

(*
 * An CVar is well-formed over subtypes of BTerm.
 *)
interactive cvar_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   <H> >- CVar{d} Type
>>

(************************************************************************
 * Derivations.
 *)

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
 * Managing the proof witness.
 *)

(*
 * These let-forms are Boolean formulas that require that
 * the indexing be in bounds, and the depths match up.
 *)
define unfold_let_sovar : let_sovar{'d; 'witness; 'i; v. 'e['v]} <-->
   spread{'witness; sovars, cvars.
      band{gt_bool{length{'sovars}; 'i};
      band{beq_int{bdepth{nth{'sovars; 'i}}; 'd};
      'e[nth{'sovars; 'i}]}}}

define unfold_let_cvar : let_cvar{'d; 'witness; 'i; v. 'e['v]} <-->
   spread{'witness; sovars, cvars.
      band{gt_bool{length{'cvars}; 'i};
      band{beq_int{bdepth{nth{'cvars; 'i}}; 'd};
      'e[nth{'cvars; 'i}]}}}

dform let_sovar_df : let_sovar{'d; 'witness; 'i; v. 'e} =
   szone pushm[0] `"let " slot{'v} `" : SOVar{" slot{'d} `"} = " slot{'witness} `".sovars.[" slot{'i} `"] in" hspace slot{'e} popm ezone

dform let_cvar_df : let_cvar{'d; 'witness; 'i; v. 'e} =
   szone pushm[0] `"let " slot{'v} `" : CVar{" slot{'d} `"} = " slot{'witness} `".cvars.[" slot{'i} `"] in" hspace slot{'e} popm ezone

(************************************************************************
 * Alpha-equality.
 *)
doc <:doc<
   Define alpha-equality on sequents.
>>
define unfold_beq_sequent : beq_sequent{'seq1; 'seq2} <--> <:xterm<
   let arg1, hyps1, goal1 = seq1 in
   let arg2, hyps2, goal2 = seq2 in
      beq_bterm{arg1; arg2} &&b beq_bterm_list{hyps1; hyps2} &&b beq_bterm{goal1; goal2}
>>

doc docoff

interactive_rw reduce_beq_sequent_cons {| reduce |} : <:xrewrite<
   beq_sequent{"sequent"{arg1; hyps1; goal1}; "sequent"{arg2; hyps2; goal2}}
   <-->
   beq_bterm{arg1; arg2} &&b beq_bterm_list{hyps1; hyps2} &&b beq_bterm{goal1; goal2}
>>

interactive beq_sequent_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- s1 IN "Sequent" -->
   "wf" : <H> >- s2 IN "Sequent" -->
   <H> >- beq_sequent{s1; s2} IN "bool"
>>

interactive beq_sequent_intro {| intro [] |} : <:xrule<
   <H> >- s1 = s2 in "Sequent" -->
   <H> >- "assert"{beq_sequent{s1; s2}}
>>

interactive beq_sequent_elim {| elim [] |} 'H : <:xrule<
   "wf" : <H>; u: "assert"{beq_sequent{s1; s2}}; <J[u]> >- s1 IN "Sequent" -->
   "wf" : <H>; u: "assert"{beq_sequent{s1; s2}}; <J[u]> >- s2 IN "Sequent" -->
   <H>; u: s1 = s2 in "Sequent"; <J[u]> >- C[u] -->
   <H>; u: "assert"{beq_sequent{s1; s2}}; <J[u]> >- C[u]
>>

(*
 * Equality on lists of Sequents.
 *)
define unfold_beq_sequent_list : beq_sequent_list{'l1; 'l2} <-->
   ball2{'l1; 'l2; t1, t2. beq_sequent{'t1; 't2}}

let fold_beq_sequent_list = makeFoldC << beq_sequent_list{'l1; 'l2} >> unfold_beq_sequent_list

interactive_rw reduce_beq_sequent_list_nil_nil {| reduce |} :
   beq_sequent_list{nil; nil}
   <-->
   btrue

interactive_rw reduce_beq_sequent_list_nil_cons {| reduce |} :
   beq_sequent_list{nil; 'u::'v}
   <-->
   bfalse

interactive_rw reduce_beq_sequent_list_cons_nil {| reduce |} :
   beq_sequent_list{'u::'v; nil}
   <-->
   bfalse

interactive_rw reduce_beq_sequent_list_cons_cons {| reduce |} :
   beq_sequent_list{'u1::'v1; 'u2::'v2}
   <-->
   band{beq_sequent{'u1; 'u2}; beq_sequent_list{'v1; 'v2}}

interactive beq_sequent_list_wf {| intro [] |} :
   [wf] sequent { <H> >- 'l1 in list{Sequent} } -->
   [wf] sequent { <H> >- 'l2 in list{Sequent} } -->
   sequent { <H> >- beq_sequent_list{'l1; 'l2} in bool }

interactive beq_sequent_list_intro {| intro [] |} :
   sequent { <H> >- 't1 = 't2 in list{Sequent} } -->
   sequent { <H> >- "assert"{beq_sequent_list{'t1; 't2}} }

interactive beq_sequent_list_elim {| elim [] |} 'H :
   [wf] sequent { <H>; u: "assert"{beq_sequent_list{'t1; 't2}}; <J['u]> >- 't1 in list{Sequent} } -->
   [wf] sequent { <H>; u: "assert"{beq_sequent_list{'t1; 't2}}; <J['u]> >- 't2 in list{Sequent} } -->
   sequent { <H>; u: 't1 = 't2 in list{Sequent}; <J['u]> >- 'C['u] } -->
   sequent { <H>; u: "assert"{beq_sequent_list{'t1; 't2}}; <J['u]> >- 'C['u] }

doc <:doc<
   Define alpha-equality on proof steps that can be used
   to specify proof rules.
>>
define unfold_beq_proof_step : beq_proof_step{'step1; 'step2} <--> <:xterm<
   let premises1, goal1 = step1 in
   let premises2, goal2 = step2 in
      beq_sequent_list{premises1; premises2} &&b beq_sequent{goal1; goal2}
>>

interactive_rw reduce_beq_proof_step {| reduce |} : <:xrewrite<
   beq_proof_step{proof_step{premises1; goal1}; proof_step{premises2; goal2}}
   <-->
   beq_sequent_list{premises1; premises2} &&b beq_sequent{goal1; goal2}
>>

interactive beq_proof_step_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- step1 IN ProofStep{"Sequent"} -->
   "wf" : <H> >- step2 IN ProofStep{"Sequent"} -->
   <H> >- beq_proof_step{step1; step2} IN "bool"
>>

interactive beq_proof_step_intro {| intro [] |} : <:xrule<
   <H> >- s1 = s2 in ProofStep{"Sequent"} -->
   <H> >- "assert"{beq_proof_step{s1; s2}}
>>

interactive beq_proof_step_elim {| elim [] |} 'H : <:xrule<
   "wf" : <H>; u: "assert"{beq_proof_step{s1; s2}}; <J[u]> >- s1 IN ProofStep{"Sequent"} -->
   "wf" : <H>; u: "assert"{beq_proof_step{s1; s2}}; <J[u]> >- s2 IN ProofStep{"Sequent"} -->
   <H>; u: s1 = s2 in ProofStep{"Sequent"}; <J[u]> >- C[u] -->
   <H>; u: "assert"{beq_proof_step{s1; s2}}; <J[u]> >- C[u]
>>

(************************************************************************
 * Display.
 *)

(*
 * Change the display of substitutions to look like
 * second-order variables.
 *)
dform subst_df : parens :: "prec"[prec_apply] :: subst{'t1; 't2} =
   szone pushm[3] slot["lt"]{'t1} `"[" slot["none"]{'t2} `"]" popm ezone

dform substl_df : parens :: "prec"[prec_apply] :: substl{'bt; 'tl} =
   szone pushm[3] slot["lt"]{'bt} `"<|" slot["none"]{'tl} `"|>" popm ezone

(*
 * Convert the term back to a sequent for display.
 *)
let no_var = Lm_symbol.add "_"
let sequent_opname = opname_of_term << "sequent"{'arg; 'hyps; 'concl} >>

let format_sequent format_term buf t =
   let arg, hyps, concl = dest_dep0_dep0_dep0_term sequent_opname t in
   let rec collect_hyps l hyps =
      if is_append_term hyps then
         let hyp, hyps = dest_append hyps in
         let hyp =
            if is_cons_term hyp then
               let h, t = dest_cons hyp in
                  if is_nil_term t then
                     h
                  else
                     hyp
            else
               hyp
         in
            collect_hyps (hyp :: l) hyps
      else
         hyps :: l
   in
   let hyps =
      List.fold_left (fun hyps h ->
            Hypothesis (no_var, h) :: hyps) [] (collect_hyps [] hyps)
   in
   let info =
      { sequent_args = arg;
        sequent_hyps = SeqHyp.of_list hyps;
        sequent_concl = concl
      }
   in
   let t = mk_sequent_term info in
      format_term buf NOParens t

ml_dform sequent_df : "sequent"{'arg; 'hyps; 'concl} format_term buf =
   format_sequent format_term buf

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
