doc <:doc<

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

   Author: Jason Hickey @email{jyh@cs.caltech.edu}
   Modified by: Xin Yu @email{xiny@cs.caltech.edu}
                Aleksey Nogin @email{nogin@cs.caltech.edu}
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
 * SOVar/CVar destructors.
 *)

(*
 * These let-forms are Boolean formulas that require that
 * the indexing be in bounds, and the depths match up.
 *)
define unfold_let_sovar : let_sovar[name:s]{'d; 'witness; 'i; v. 'e['v]} <-->
   spread{'witness; sovars, cvars.
      band{gt_bool{length{'sovars}; 'i};
      band{beq_int{bdepth{nth{'sovars; 'i}}; 'd};
      'e[nth{'sovars; 'i}]}}}

define unfold_let_cvar : let_cvar[name:s]{'d; 'witness; 'i; v. 'e['v]} <-->
   spread{'witness; sovars, cvars.
      band{gt_bool{length{'cvars}; 'i};
      band{bhyp_depths{'d; nth{'cvars; 'i}};
      'e[nth{'cvars; 'i}]}}}

dform let_sovar_df : let_sovar[name:s]{'d; 'witness; 'i; v. 'e} =
   szone pushm[0] `"let " slot{'v} `"(" slot[name:s] `") : BTerm{" slot{'d} `"} = " slot{'witness} `".sovars.[" slot{'i} `"] in" hspace slot{'e} popm ezone

dform let_cvar_df : let_cvar[name:s]{'d; 'witness; 'i; v. 'e} =
   szone pushm[0] `"let " slot{'v} `"(" slot[name:s] `") : CVar{" slot{'d} `"} = " slot{'witness} `".cvars.[" slot{'i} `"] in" hspace slot{'e} popm ezone

interactive_rw reduce_let_sovar {| reduce |} : <:xrewrite<
   "let_sovar"[name:s]{d; proof_step_witness{sovars; cvars}; i; v. e[v]}
   <-->
   band{gt_bool{length{sovars}; i};
   band{beq_int{bdepth{nth{sovars; i}}; d};
   e[nth{sovars; i}]}}
>>

interactive_rw reduce_let_cvar {| reduce |} : <:xrewrite<
   "let_cvar"[name:s]{d; proof_step_witness{sovars; cvars}; i; v. e[v]}
   <-->
   band{gt_bool{length{cvars}; i};
   band{bhyp_depths{d; nth{cvars; i}};
   e[nth{cvars; i}]}}
>>

interactive let_sovar_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d in nat -->
   "wf" : <H> >- witness IN ProofStepWitness -->
   "wf" : <H> >- i in nat -->
   "wf" : <H>; v: BTerm{d} >- e[v] in bool -->
   <H> >- "let_sovar"[name:s]{d; witness; i; v. e[v]} in bool
>>

interactive let_cvar_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d in nat -->
   "wf" : <H> >- witness IN "ProofStepWitness" -->
   "wf" : <H> >- i in nat -->
   "wf" : <H>; v: CVar{d} >- e[v] in bool -->
   <H> >- "let_cvar"[name:s]{d; witness; i; v. e[v]} in bool
>>

interactive let_sovar_elim {| elim [] |} 'H :
   [wf] sequent { <H>; x: "assert"{let_sovar[name:s]{'d; 'witness; 'i; v. 'e['v]}}; <J['x]> >- 'witness in ProofStepWitness } -->
   [wf] sequent { <H>; x: "assert"{let_sovar[name:s]{'d; 'witness; 'i; v. 'e['v]}}; <J['x]> >- 'i in nat } -->
   [wf] sequent { <H>; x: "assert"{let_sovar[name:s]{'d; 'witness; 'i; v. 'e['v]}}; <J['x]> >- 'd in nat } -->
   sequent { <H>; u: BTerm{'d}; "assert"{'e['u]}; <J[it]> >- 'C[it] } -->
   sequent { <H>; x: "assert"{let_sovar[name:s]{'d; 'witness; 'i; v. 'e['v]}}; <J['x]> >- 'C['x] }

interactive let_cvar_elim {| elim [] |} 'H :
   [wf] sequent { <H>; x: "assert"{let_cvar[name:s]{'d; 'witness; 'i; v. 'e['v]}}; <J['x]> >- 'witness in ProofStepWitness } -->
   [wf] sequent { <H>; x: "assert"{let_cvar[name:s]{'d; 'witness; 'i; v. 'e['v]}}; <J['x]> >- 'i in nat } -->
   [wf] sequent { <H>; x: "assert"{let_cvar[name:s]{'d; 'witness; 'i; v. 'e['v]}}; <J['x]> >- 'd in nat } -->
   sequent { <H>; u: CVar{'d}; "assert"{bhyp_depths{'d; 'u}}; "assert"{'e['u]}; <J[it]> >- 'C[it] } -->
   sequent { <H>; x: "assert"{let_cvar[name:s]{'d; 'witness; 'i; v. 'e['v]}}; <J['x]> >- 'C['x] }

(************************************************************************
 * Terms.
 *)
let is_let_cvar_term t =
   match explode_term t with
      << let_cvar[name:s]{'d; 'witness; 'i; v. 'e} >> ->
         true
    | _ ->
         false

let dest_let_cvar_term t =
   match explode_term t with
      << let_cvar[name:s]{'d; 'witness; 'i; v. 'e} >> ->
         name, d, witness, i, v, e
    | _ ->
         raise (RefineError ("dest_let_cvar_term", StringTermError ("not a let_cvar term", t)))

let is_let_sovar_term t =
   match explode_term t with
      << let_sovar[name:s]{'d; 'witness; 'i; v. 'e} >> ->
         true
    | _ ->
         false

let dest_let_sovar_term t =
   match explode_term t with
      << let_sovar[name:s]{'d; 'witness; 'i; v. 'e} >> ->
         name, d, witness, i, v, e
    | _ ->
         raise (RefineError ("dest_let_sovar_term", StringTermError ("not a let_sovar term", t)))

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
