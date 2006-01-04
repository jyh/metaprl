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
open Itt_equal

doc <:doc<
   A sequent is represented as a 3-tuple << BTerm * list{BTerm} * BTerm >>,
   where the first term is the argument, the second is the hypotheses,
   and the final term is the conclusion.
>>
define unfold_sequent : "sequent"{'arg; 'hyps; 'concl} <-->
   ('arg, ('hyps, 'concl))

define unfold_sequent_arg : sequent_arg{'s} <-->
   fst{'s}

define unfold_sequent_hyps : sequent_hyps{'s} <-->
   fst{snd{'s}}

define unfold_sequent_concl : sequent_concl{'s} <-->
   snd{snd{'s}}

doc <:doc<
   A sequent is well-formed only if the hypotheses have depths increasing
   by one, and the conclusion is also at the right nesting depth.

   The << hyp_depths{'d; 'l} >> predicate tests whether the list << 'l >>
   is a valid list of terms with binding depths started with << 'd >>.
>>
(* XXX: BUG: define the propositional form using assert *)
define unfold_hyp_depths : hyp_depths{'d; 'l} <-->
   list_ind{'l; lambda{d. "true"}; h, t, g. lambda{d. bdepth{'h} = 'd in nat & 'g ('d +@ 1)}} 'd

define unfold_bhyp_depths : bhyp_depths{'d; 'l} <-->
   list_ind{'l; lambda{d. "btrue"}; h, t, g. lambda{d. band{beq_int{bdepth{'h}; 'd}; 'g ('d +@ 1)}}} 'd

doc <:doc<
   The << is_sequent{'d; 's} >> predicate tests whether a sequent << 's >> is well-formed
   with respect to binding depths.
   The argument must have depth << 0 >>, the hypotheses must have binding depths
   starting with << 'd >>, and the conclusion must have binding depth
   << length{'hyps} +@ 'd >>.
>>
define unfold_is_sequent_depth : is_sequent{'d; 's} <-->
   spread{'s; arg, rest. spread{'rest; hyps, concl.
      bdepth{'arg} = 0 in nat
      & hyp_depths{'d; 'hyps}
      & bdepth{'concl} = length{'hyps} +@ 'd in nat}}

define unfold_is_sequent : is_sequent{'s} <-->
   spread{'s; arg, rest. spread{'rest; hyps, concl.
      bdepth{'arg} = 0 in nat
      & hyp_depths{0; 'hyps}
      & bdepth{'concl} = length{'hyps} in nat}}

doc <:doc<
   The term << Sequent >> represents the type of sequents.
>>
define unfold_Sequent_depth : Sequent{'d} <-->
   { s: BTerm * list{BTerm} * BTerm | is_sequent{'d; 's} }

define const unfold_Sequent : Sequent <-->
   { s: BTerm * list{BTerm} * BTerm | is_sequent{'s} }

doc <:doc<
   The << CVar{'d} >> represents a sequent context at binding depth << 'd >>.
>>
define unfold_CVar : CVar{'d} <-->
   { l: list{BTerm} | hyp_depths{'d; 'l} }

doc docoff

let fold_hyp_depths = makeFoldC << hyp_depths{'d; 'l} >> unfold_hyp_depths
let fold_bhyp_depths = makeFoldC << bhyp_depths{'d; 'l} >> unfold_bhyp_depths
let fold_sequent = makeFoldC << "sequent"{'arg; 'hyps; 'goal} >> unfold_sequent

(*
 * hyp_depths rules.
 *)
interactive_rw reduce_hyp_depths_nil {| reduce |} : <:xrewrite<
   hyp_depths{d; "nil"}
   <-->
   "true"
>>

interactive_rw reduce_hyp_depths_cons {| reduce |} : <:xrewrite<
   hyp_depths{d; u::v}
   <-->
   bdepth{u} = d in "nat" && hyp_depths{d +@ 1; v}
>>

interactive hyp_depths_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   "wf" : <H> >- l IN list{"BTerm"} -->
   <H> >- hyp_depths{d; l} Type
>>

(*
 * bhyp_depths (Boolean version).
 *)
interactive_rw reduce_bhyp_depths_nil {| reduce |} : <:xrewrite<
   bhyp_depths{d; "nil"}
   <-->
   "btrue"
>>

interactive_rw reduce_bhyp_depths_cons {| reduce |} : <:xrewrite<
   bhyp_depths{d; u::v}
   <-->
   beq_int{bdepth{u}; d} &&b bhyp_depths{d +@ 1; v}
>>

interactive bhyp_depths_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   "wf" : <H> >- l IN list{"BTerm"} -->
   <H> >- bhyp_depths{d; l} IN "bool"
>>

interactive bhyp_depths_intro {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   "wf" : <H> >- l IN list{"BTerm"} -->
   <H> >- hyp_depths{d; l} -->
   <H> >- "assert"{bhyp_depths{d; l}}
>>

interactive bhyp_depths_elim {| elim [] |} 'H : <:xrule<
   "wf" : <H>; u: "assert"{bhyp_depths{d; l}}; <J[u]> >- d IN "nat" -->
   "wf" : <H>; u: "assert"{bhyp_depths{d; l}}; <J[u]> >- l IN list{"BTerm"} -->
   <H>; hyp_depths{d; l}; <J["it"]> >- C["it"] -->
   <H>; u: "assert"{bhyp_depths{d; l}}; <J[u]> >- C[u]
>>

(*
 * is_sequent is well-formed if applied to a sequent triple.
 *)
interactive is_sequent_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- s IN "BTerm" * list{"BTerm"} * "BTerm" -->
   <H> >- is_sequent{s} Type
>>

interactive is_sequent_depth_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   "wf" : <H> >- s IN "BTerm" * list{"BTerm"} * "BTerm" -->
   <H> >- is_sequent{d; s} Type
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

interactive is_sequent_depth_wf2 {| intro [] |} : <:xrule<
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

interactive sequent_term_equal {| intro [] |} : <:xrule<
   "wf" : <H> >- arg1 = arg2 in BTerm -->
   "wf" : <H> >- hyps1 = hyps2 in list{BTerm} -->
   "wf" : <H> >- concl1 = concl2 in BTerm -->
   "wf" : <H> >- bdepth{arg1} = 0 in nat -->
   "wf" : <H> >- hyp_depths{0; hyps1} -->
   "wf" : <H> >- bdepth{concl1} = length{hyps1} in nat -->
   <H> >- "sequent"{arg1; hyps1; concl1} = "sequent"{arg2; hyps2; concl2} in Sequent
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
 * An CVar is well-formed over subtypes of BTerm.
 *)
interactive cvar_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   <H> >- CVar{d} Type
>>

(*
 * Sequent projections.
 *)
interactive_rw reduce_sequent_arg {| reduce |} : <:xrewrite<
   sequent_arg{"sequent"{arg; hyps; concl}}
   <-->
   arg
>>

interactive_rw reduce_sequent_hyps {| reduce |} : <:xrewrite<
   sequent_hyps{"sequent"{arg; hyps; concl}}
   <-->
   hyps
>>

interactive_rw reduce_sequent_concl {| reduce |} : <:xrewrite<
   sequent_concl{"sequent"{arg; hyps; concl}}
   <-->
   concl
>>

interactive_rw reduce_is_sequent {| reduce |} : <:xrewrite<
   is_sequent{"sequent"{arg; hyps; concl}}
   <-->
   bdepth{arg} = 0 in "nat"
   && hyp_depths{0; hyps}
   && bdepth{concl} = length{hyps} in "nat"
>>

interactive sequent_arg_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d = 0 in "nat" -->
   "wf" : <H> >- s IN "Sequent" -->
   <H> >- sequent_arg{s} IN BTerm{d}
>>

interactive sequent_hyps_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d = 0 in "nat" -->
   "wf" : <H> >- s IN "Sequent" -->
   <H> >- sequent_hyps{s} IN CVar{d}
>>

interactive sequent_concl_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d = length{sequent_hyps{s}} in "nat" -->
   "wf" : <H> >- s IN "Sequent" -->
   <H> >- sequent_concl{s} IN BTerm{d}
>>

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

(************************************************************************
 * Sequents with depths.
 *)
interactive sequent_depth_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   <H> >- Sequent{d} Type
>>

interactive sequent_depth_elim :
   [wf] sequent { <H> >- 'e in Sequent{0} } -->
   sequent { <H> >- 'e in Sequent }

interactive sequent_depth_mem {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   "wf" : <H> >- arg IN BTerm{0} -->
   "wf" : <H> >- hyps IN CVar{d} -->
   "wf" : <H> >- concl IN BTerm{length{hyps} +@ d} -->
   <H> >- "sequent"{arg; hyps; concl} IN Sequent{d}
>>

(************************************************************************
 * Additional well-formedness.
 *)
doc <:doc<
   Additional well-formedness theorems for the various types.
>>
interactive cvar_nil_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   <H> >- [] IN CVar{d}
>>

interactive cvar_cons_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   "wf" : <H> >- u IN BTerm{d} -->
   "wf" : <H> >- v IN CVar{d +@ 1} -->
   <H> >- u::v IN CVar{d}
>>

interactive cvar_append_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   "wf" : <H> >- l1 IN CVar{d} -->
   "wf" : <H> >- l2 IN CVar{d +@ length{l1}} -->
   <H> >- append{l1; l2} IN CVar{d}
>>

interactive cvar_is_list {| intro [intro_typeinf << 'l >>] |} CVar{'n} : <:xrule<
   "wf" : <H> >- n IN "nat" -->
   "wf" : <H> >- l IN CVar{n} -->
   <H> >- l IN "list"
>>

(************************************************************************
 * Forward chaining rules.
 *)
doc <:doc<
   Forward-chaining.
>>
interactive cvar_forward {| forward [] |} 'H : <:xrule<
   "wf" : <H>; l in CVar{n}; <J> >- n in nat -->
   <H>; l in CVar{n}; <J>; l in list{BTerm}; hyp_depths{n; l} >- 'C -->
   <H>; l in CVar{n}; <J> >- 'C
>>

interactive append_cvar_elim {| forward [] |} 'H : <:xrule<
   "wf" : <H>; append{l1; l2} in CVar{d}; <J> >- d in nat -->
   "wf" : <H>; append{l1; l2} in CVar{d}; <J> >- l1 in list{BTerm} -->
   "wf" : <H>; append{l1; l2} in CVar{d}; <J> >- l2 in list{BTerm} -->
   <H>; append{l1; l2} in CVar{d}; <J>; l1 in CVar{d}; l2 in CVar{d +@ length{l1}} >- C -->
   <H>; append{l1; l2} in CVar{d}; <J> >- C
>>

(************************************************************************
 * Display.
 *)

(*
 * Change the display of substitutions to look like
 * second-order variables.
 *)
dform subst_df : parens :: "prec"[prec_apply] :: subst{'t1; 't2} =
   szone pushm[3] slot["lt"]{'t1} `"@[" slot["none"]{'t2} `"]" popm ezone

dform substl_df : parens :: "prec"[prec_apply] :: substl{'bt; 'tl} =
   szone pushm[3] slot["lt"]{'bt} `"@<|" slot["none"]{'tl} `"|>" popm ezone

dform beq_sequent_df : parens :: "prec"[prec_equal] :: beq_sequent{'s1; 's2} =
   szone pushm[3] slot{'s1} hspace `"=seq " slot{'s2} popm ezone

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

(*
ml_dform sequent_df : "sequent"{'arg; 'hyps; 'concl} format_term buf =
   format_sequent format_term buf
 *)

(************************************************************************
 * Terms.
 *)
let beq_sequent_term = << beq_sequent{'step1; 'step2} >>
let beq_sequent_opname = opname_of_term beq_sequent_term
let is_beq_sequent_term = is_dep0_dep0_term beq_sequent_opname
let dest_beq_sequent_term = dest_dep0_dep0_term beq_sequent_opname

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
