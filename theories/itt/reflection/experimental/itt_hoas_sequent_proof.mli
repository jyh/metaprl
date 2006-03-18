doc <:doc<
   Provability in a sequent logic.

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

(*
 * Provability in a sequent logic.
 *)
declare ProvableSequent{'logic; 'seq}

(*
 * Judgments in a sequent logic.
 *)
declare IsJudgment{'logic; 'seq}
declare ProvableJudgment{'logic; 'seq}

(************************************************************************
 * Tactics.
 *)

(*
 * The main tactic for proving Provable theorems.
 *)
topval provableRuleT : term -> conv -> tactic

(************************************************
 * Debugging.
 *)
topval assumAllT : tactic
topval provableIntroT : tactic
topval proofStepWitnessT : tactic
topval provableRuleStartT : term -> conv -> tactic
topval provable_forwardT : int -> tactic

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
