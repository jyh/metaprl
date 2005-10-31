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
extends Itt_srec
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
   The term << ValidStep{'step; 'logic} >> is the predicate that determines
   if the proof step matches one of the proof rules in the logic.
>>
define unfold_ValidStep : ValidStep{'step; 'logic} <-->
   exists_list{'logic; check. 'check (spread{'step; premises, goal. (map{x. snd{'x}; 'premises}, 'goal)})}

doc <:doc<
   The term << Derivation{'ty_sequent; 'logic} >> represents the set of
   valid derivations in the logic.
>>
define unfold_Derivation : Derivation{'ty_sequent; 'logic} <-->
   srec{T. { step: (list{'T} * 'ty_sequent) | "subtype"{'T; top * 'ty_sequent} & ValidStep{'step; 'logic} }}

doc docoff

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
 * The step discards some of the information.
 *)
interactive derivation_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- ty_sequent IN "univ"[1:l] -->
   "wf" : <H> >- logic IN "Logic"{ty_sequent} -->
   <H> >- "Derivation"{ty_sequent; logic} Type
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
