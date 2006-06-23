doc <:doc<

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
extends Itt_hoas_sequent_proof

doc docoff

open Basic_tactics

(************************************************************************
 * Basic rules tactics.
 *)
interactive cvar_elim1 {| intro [intro_typeinf << 'C >>] |} CVar{'i} : <:xrule<
   "wf" : <H> >- C IN CVar{i} -->
   <H> >- C IN list{"BTerm"}
>>

interactive hyp_depths_elim1 {| intro [] |} : <:xrule<
   "wf" : <H> >- C IN CVar{i} -->
   <H> >- hyp_depths{i; C}
>>

(************************************************************************
 * Tactics for proving well-formedness of rule checkers.
 *)
interactive proof_rule_wf1 {| intro [] |} : <:xrule<
   "wf" : <H> >- ty_sequent Type -->
   "wf" : <H>; step: ProofStep{ty_sequent}; witness: "ProofStepWitness" >- e[step; witness] IN "bool" -->
   <H> >-
      lambda{proof_step. spread{proof_step; step, witness. e[step; witness]}}
      IN ProofRule{ty_sequent}
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
