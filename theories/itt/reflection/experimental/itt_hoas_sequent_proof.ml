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
extends Itt_hoas_sequent
extends Itt_hoas_proof

doc docoff

open Dform
open Basic_tactics

open Itt_list
open Itt_list2
open Itt_dfun

(************************************************************************
 * Alpha-equality.
 *)
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
 * SOVar/CVar destructors.
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
      band{bhyp_depths{'d; nth{'cvars; 'i}};
      'e[nth{'cvars; 'i}]}}}

dform let_sovar_df : let_sovar{'d; 'witness; 'i; v. 'e} =
   szone pushm[0] `"let " slot{'v} `" : SOVar{" slot{'d} `"} = " slot{'witness} `".sovars.[" slot{'i} `"] in" hspace slot{'e} popm ezone

dform let_cvar_df : let_cvar{'d; 'witness; 'i; v. 'e} =
   szone pushm[0] `"let " slot{'v} `" : CVar{" slot{'d} `"} = " slot{'witness} `".cvars.[" slot{'i} `"] in" hspace slot{'e} popm ezone
interactive_rw reduce_let_sovar {| reduce |} : <:xrewrite<
   let_sovar{d; proof_step_witness{sovars; cvars}; i; v. e[v]}
   <-->
   band{gt_bool{length{sovars}; i};
   band{beq_int{bdepth{nth{sovars; i}}; d};
   e[nth{sovars; i}]}}
>>

interactive_rw reduce_let_cvar {| reduce |} : <:xrewrite<
   let_cvar{d; proof_step_witness{sovars; cvars}; i; v. e[v]}
   <-->
   band{gt_bool{length{cvars}; i};
   band{bhyp_depths{d; nth{cvars; i}};
   e[nth{cvars; i}]}}
>>

interactive let_sovar_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   "wf" : <H> >- witness IN "ProofStepWitness" -->
   "wf" : <H> >- i IN "nat" -->
   "wf" : <H>; v: SOVar{d} >- e[v] IN "bool" -->
   <H> >- let_sovar{d; witness; i; v. e[v]} IN "bool"
>>

interactive let_cvar_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   "wf" : <H> >- witness IN "ProofStepWitness" -->
   "wf" : <H> >- i IN "nat" -->
   "wf" : <H>; v: CVar{d} >- e[v] IN "bool" -->
   <H> >- let_cvar{d; witness; i; v. e[v]} IN "bool"
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
