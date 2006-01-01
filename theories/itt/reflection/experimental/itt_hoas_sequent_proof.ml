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
extends Itt_hoas_sequent
extends Itt_hoas_proof

doc docoff

open Basic_tactics
open Itt_list

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
