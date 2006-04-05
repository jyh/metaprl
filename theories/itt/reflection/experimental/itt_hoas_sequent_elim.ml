doc <:doc<
   @module[Itt_hoas_sequent_elim]

   The @tt[Itt_hoas_sequent_elim] module defines the tactic for
   proving the proof induction term.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2006 MetaPRL Group, California Institute of Technology

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

   Author: Aleksey Nogin @email{nogin@cs.caltech.edu}

   @end[license]
   @parents
>>
extends Itt_hoas_proof
extends Itt_hoas_proof_ind
extends Itt_hoas_sequent
extends Itt_hoas_sequent_bterm
extends Itt_hoas_sequent_proof

doc docoff

open Basic_tactics
open Itt_struct
open Itt_logic
open Itt_hoas_bterm_wf
open Itt_hoas_proof
open Itt_hoas_sequent_proof_step
open Itt_hoas_proof_ind

doc <:doc< @rules >>

interactive provable_to_provable_sequent 'H :
   [wf] sequent { <H>; Provable{'logic; 'seq}; <J> >- 'seq in BSequent } -->
   sequent { <H>; ProvableSequent{'logic; 'seq}; <J> >- 'C } -->
   sequent { <H>; Provable{'logic; 'seq}; <J> >- 'C }

doc docoff

let rec all_and_alim i p =
   if i > (hyp_count p) then
      idT
   else if is_and_term (nth_hyp p i) then begin
      and_elim i
      thenMT (
         (provable_to_provable_sequent i thenMT argfunT all_and_alim (i + 1))
         orelseT argfunT all_and_alim i)
   end else
      argfunT all_and_alim (i+1)

let proofCheckElimT = argfunT (fun i p ->
   match explode_term (nth_hyp p i) with
      << ProofCheck{'_rule; 'premises; 'goal; 'witness} >> ->
         dT i thenT thinT i
         thenMT repeatForT 2 (moveHypT i (-3))
         thenMT hypSubstT (-2) (-4)
         thenMT hypSubstT (-2) (-3)
         thenMT thinT (-2)
         thenMT thinT 6
         thenMT moveHypT 5 (-2)
         thenMT simpleReduceT
         thenMT argfunT all_and_alim 5
    | _ -> idT)

let elimRuleT =
   rwhAllAll reduceC 
   thenMT provableSequent_elim 2 
   thenMT dT 8
   thenMT proofCheckElimT 8
   (* XXX: incomplete *)
   thenT proofRuleWFT

let elimRuleStartT =
   provableSequent_elim 2 ta

let elimSimpleStepT unfold =
   rw (addrC [Subterm 4] unfold) 2
   thenT repeatMT (firstT [
      step_rules_logic_cons 2;
      step_union_logic_elim 2;
      step_rules_logic_nil 2
   ])
   thenT autoT

let rec var_elimT i p =
   (* XXX: TODO: use "p" instead of guessing with orelseT *)
   (let_cvar_elim i thenMT rw reduceC (i + 2) thenMT argfunT var_elimT (i + 2))
   orelseT
   (let_sovar_elim i thenMT rw reduceC (i + 1) thenMT argfunT var_elimT (i + 1))
   orelseT
   idT

let elimProofCheckT unfold =
   dupHypT 2
   thenT rw (addrC [Subterm 1] unfold) 4
   thenT proofCheck_elim 4 thenT thinT 4 thenT thinT 5
   thenT simpleReduceT
   thenT argfunT var_elimT 4
   thenMT dT (-4) thenMT dT (-4) thenMT dT (-5)
   thenMT rwcAll reduceC 1
   thenT proofRuleWFT

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
