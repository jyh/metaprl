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

open Basic_tactics

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
   The << is_sequent{'d; 's} >> predicate tests whether a sequent is well-formed
   with respect to binding depths.  If the binding depth of the sequent is << 'd >>,
   then the argument must have depth << 'd >>, the hypotheses must have binding depths
   starting with << 'd >>, and the conclusion must have binding depth
   << 'd +@ length{'hyps} >>.
>>
define unfold_is_sequent : is_sequent{'d; 's} <-->
   spread{'s; arg, rest. spread{'rest; hyps, concl.
      bdepth{'arg} = 'd in nat
      & hyp_depths{'d; 'hyps}
      & bdepth{'concl} = 'd +@ length{'hyps} in nat}}

doc <:doc<
   A term << Sequent{'d; 'ty_arg; 'ty_hyps; 'ty_concl} >> is the type of
   sequents at binding depth << 'd >>.  The argument must have type
   << 'ty_arg >>, each hypothesis must have type << 'ty_hyps >>, and the
   conclusion must have type << 'ty_concl >>.
>>
define unfold_Sequent : Sequent{'d; 'ty_arg; 'ty_hyp; 'ty_concl} <-->
   { s: ('ty_arg * list{'ty_hyp} * 'ty_concl) | is_sequent{'d; 's} }

doc <:doc<
   The << SOVar{'d; 'ty} >> term represents a second-order variable of type
   << 'ty >> at binding depth << 'd >>.
>>
define unfold_SOVar : SOVar{'d; 'ty} <-->
   { e: 'ty | bdepth{'e} = 'd in nat }

doc <:doc<
   The << CVar{'d; 'ty} >> represents a sequent context at binding depth << 'd >>.
   The sequent context represents a list of hypotheses of type << 'ty >>.
>>
define unfold_CVar : CVar{'d; 'ty} <-->
   { l: list{'ty} | hyp_depths{'d; 'l} }

doc <:doc<
   A proof step << ProofStep{'ty_sequent} >> represents one rule application
   in a proof.  The proof step has a list of premises, and a goal.
>>
define unfold_ProofStep : ProofStep{'ty_sequent} <-->
   list{'ty_sequent} * 'ty_sequent

doc docoff

let fold_hyp_depths = makeFoldC << hyp_depths{'d; 'l} >> unfold_hyp_depths

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
   "wf" : <H> >- d IN "nat" -->
   "wf" : <H> >- s IN "BTerm" * list{"BTerm"} * "BTerm" -->
   <H> >- is_sequent{d; s} Type
>>

(*
 * This is similar, but we have an explicit sequent triple.
 *)
interactive is_sequent_wf2 {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   "wf" : <H> >- arg IN "BTerm" -->
   "wf" : <H> >- hyps IN list{"BTerm"} -->
   "wf" : <H> >- concl IN "BTerm" -->
   <H> >- is_sequent{d; "sequent"{arg; hyps; concl}} Type
>>

(*
 * The Sequent type is well-formed if all the types are subtypes
 * of BTerm.
 *)
interactive sequent_wf {| intro [] |} : <:xrule<
   "aux" : <H> >- "subtype"{ty_arg; "BTerm"} -->
   "aux" : <H> >- "subtype"{ty_hyp; "BTerm"} -->
   "aux" : <H> >- "subtype"{ty_concl; "BTerm"} -->
   "wf" : <H> >- d IN "nat" -->
   <H> >- Sequent{d; ty_arg; ty_hyp; ty_concl} Type
>>

(*
 * An actual sequent has the sequent type if the types
 * and depths match up.
 *)
interactive sequent_term_wf {| intro [] |} : <:xrule<
   "aux" : <H> >- "subtype"{ty_arg; "BTerm"} -->
   "aux" : <H> >- "subtype"{ty_hyp; "BTerm"} -->
   "aux" : <H> >- "subtype"{ty_concl; "BTerm"} -->
   "wf" : <H> >- d IN "nat" -->
   "wf" : <H> >- arg IN ty_arg -->
   "wf" : <H> >- hyps IN list{ty_hyp} -->
   "wf" : <H> >- concl IN ty_concl -->
   "wf" : <H> >- bdepth{arg} = d in "nat" -->
   "wf" : <H> >- hyp_depths{d; hyps} -->
   "wf" : <H> >- bdepth{concl} = d +@ length{hyps} in "nat" -->
   <H> >- "sequent"{arg; hyps; concl} IN Sequent{d; ty_arg; ty_hyp; ty_concl}
>>

(*
 * An SOVar is well-formed over subtypes of BTerm.
 *)
interactive sovar_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   "wf" : <H> >- "subtype"{ty; "BTerm"} -->
   <H> >- SOVar{d; ty} Type
>>

(*
 * An CVar is well-formed over subtypes of BTerm.
 *)
interactive cvar_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   "wf" : <H> >- "subtype"{ty; "BTerm"} -->
   <H> >- CVar{d; ty} Type
>>

(*
 * A proof step can range over any type.
 *)
interactive proof_step_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- ty Type -->
   <H> >- ProofStep{ty} Type
>>

(************************************************************************
 * Derivations.
 *)

doc <:doc<
   The term << ProofRule{'ty} >> represents a proof checker for
   proof steps with terms of type << 'ty >>.
>>
define unfold_ProofRule : ProofRule{'ty} <-->
   ProofStep{'ty} -> univ[1:l]

doc <:doc<
   The term << Logic{'ty} >> represents a set of proof rules.
>>
define unfold_Logic : Logic{'ty} <-->
   list{ProofRule{'ty}}

doc <:doc<
   A derivation has three parts, 1) the premises << DerivationPremises{'d} >>,
   the goal << DerivationGoal{'d} >>, and the justification.
>>
define unfold_DerivationPremises : DerivationPremises{'d} <-->
   fst{'d}

define unfold_DerivationGoal : DerivationGoal{'d} <-->
   fst{snd{'d}}

doc <:doc<
   The term << ValidStep{'premises; 'goal; 'logic} >> is the predicate that determines
   if the proof step matches one of the proof rules in the logic.
>>
define unfold_ValidStep : ValidStep{'premises; 'goal; 'logic} <-->
   exists_list{'logic; check. 'check (map{x. DerivationGoal{'x}; 'premises}, 'goal)}

doc <:doc<
   A << DerivationStep{'premises; 'goal; 'p} >> forms one step of a derivation,
   where << 'p >> is the proof that the << 'goal >> follows from the << 'premises >>.
>>
define unfold_DerivationStep : DerivationStep{'premises; 'goal; 'p} <-->
   pair{'premises; pair{'goal; 'p}}

doc <:doc<
   The term << Derivation{'ty_sequent; 'logic} >> represents the set of
   valid derivations in the logic.  We define it as the finite unrollings of
   proof trees.
>>
define unfold_Derivation_indexed : Derivation{'n; 'ty_sequent; 'logic} <-->
   ind{'n; void; m, T. premises: list{'T} * goal: 'ty_sequent * ValidStep{'premises; 'goal; 'logic}}

define unfold_Derivation : Derivation{'ty_sequent; 'logic} <-->
   tunion{nat; n. Derivation{'n; 'ty_sequent; 'logic}}
doc docoff

let fold_Logic = makeFoldC << Logic{'ty_sequent} >> unfold_Logic
let fold_DerivationStep = makeFoldC << DerivationStep{'premises; 'goal; 'proof} >> unfold_DerivationStep
let fold_Derivation_indexed = makeFoldC << Derivation{'n; 'ty_sequent; 'logic} >> unfold_Derivation_indexed

(*
 * A ProofRule is a type for any type.
 *)
interactive proof_rule_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- ty Type -->
   <H> >- "ProofRule"{ty} Type
>>

interactive logic_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- ty Type -->
   <H> >- "Logic"{ty} Type
>>

(*
 * A ValidStep requires a derivation and a goal.
 *)
interactive derivation_premises_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- t IN ty_premises * "top" * "top" -->
   <H> >- DerivationPremises{t} IN ty_premises
>>

interactive derivation_goal_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- t IN "top" * ty_sequent * "top" -->
   <H> >- DerivationGoal{t} IN ty_sequent
>>

interactive valid_step_wf {| intro [intro_typeinf << 'goal >>] |} 'ty_sequent : <:xrule<
   "wf" : <H> >- ty_sequent Type -->
   "wf" : <H> >- premises IN list{"top" * ty_sequent * "top"} -->
   "wf" : <H> >- goal IN ty_sequent -->
   "wf" : <H> >- logic IN Logic{ty_sequent} -->
   <H> >- ValidStep{premises; goal; logic} Type
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
   Prod premises: list{Derivation{n; ty_sequent; logic}} * Prod goal: ty_sequent * ValidStep{premises; goal; logic}
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
   "wf" : <H> >- logic IN Logic{ty_sequent} -->
   <H> >- ValidStep{premises; goal; logic} Type
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

(*
 * The depth of a derivation is computable.
 *)
define unfold_DerivationDepth : DerivationDepth{'d} <--> <:xterm<
   (fix depth d ->
       list_max{map{premise. depth premise; DerivationPremises{d}}} +@ 1) d
>>

let fold_DerivationDepth = makeFoldC << DerivationDepth{'d} >> unfold_DerivationDepth

interactive derivation_depth_wf1 {| intro [intro_typeinf << 'd >>] |} Derivation{'n; 'ty_sequent; 'ty_logic} : <:xrule<
   "wf" : <H> >- n IN "nat" -->
   "wf" : <H> >- ty_sequent Type -->
   "wf" : <H> >- ty_logic IN Logic{ty_sequent} -->
   "wf" : <H> >- d IN Derivation{n; ty_sequent; ty_logic} -->
   <H> >- DerivationDepth{d} IN "nat"
>>

interactive derivation_depth_wf {| intro [intro_typeinf << 'd >>] |} Derivation{'ty_sequent; 'ty_logic} : <:xrule<
   "wf" : <H> >- ty_sequent Type -->
   "wf" : <H> >- ty_logic IN Logic{ty_sequent} -->
   "wf" : <H> >- d IN Derivation{ty_sequent; ty_logic} -->
   <H> >- DerivationDepth{d} IN "nat"
>>

interactive derivation_depth_elim {| elim [] |} 'H : <:xrule<
   "wf" : <H>; e: Derivation{ty_sequent; logic}; <J[e]> >- ty_sequent Type -->
   "wf" : <H>; e: Derivation{ty_sequent; logic}; <J[e]> >- logic IN Logic{ty_sequent} -->
   <H>; e: Derivation{ty_sequent; logic}; <J[e]>; e IN Derivation{DerivationDepth{e}; ty_sequent; logic} >- C[e] -->
   <H>; e: Derivation{ty_sequent; logic}; <J[e]> >- C[e]
>>

interactive derivation_depth_bound {| intro [intro_typeinf << 'e >>] |} Derivation{'n; 'ty_sequent; 'logic} : <:xrule<
   "wf" : <H> >- n IN "nat" -->
   "wf" : <H> >- ty_sequent Type -->
   "wf" : <H> >- logic IN Logic{ty_sequent} -->
   "wf" : <H> >- e IN Derivation{n; ty_sequent; logic} -->
   <H> >- DerivationDepth{e} <= n
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
       all_list{premises; premise. P[premise]};
       p: ValidStep{premises; goal; logic} >- P[DerivationStep{premises; goal; p}] -->
   <H>; e: Derivation{ty_sequent; logic}; <J[e]> >- P[e]
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
