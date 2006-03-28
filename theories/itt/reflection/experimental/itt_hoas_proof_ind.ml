doc <:doc<
   @module[Itt_hoas_proof_ind]

   The @tt[Itt_hoas_proof_ind] module establishes the generic proof
   induction rules.

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

   Authors:
      Xin Yu @email{xiny@cs.caltech.edu}
      Aleksey Nogin @email{nogin@cs.caltech.edu}

   @end[license]
   @parents
>>
extends Itt_hoas_proof
extends Itt_hoas_sequent_bterm
extends Itt_hoas_sequent_proof

doc docoff

open Basic_tactics

doc rules

interactive provable_elim 'H :
   [wf] sequent { <H>; v: 'ty; x: Provable{'logic; 'A['v]}; <J['v; 'x]> >- 'logic in Logic } -->
   [wf] sequent { <H>; v: 'ty; x: Provable{'logic; 'A['v]}; <J['v; 'x]>; w: 'ty >- 'A['w] in BTerm } -->
   sequent { <H>; v: 'ty; x: Provable{'logic; 'A['v]}; <J['v; 'x]>;
       u: 'ty;
       premises: list{Derivation{'logic}};
       witness: ProofStepWitness;
       ValidStep{'premises; 'A['u]; 'witness; 'logic};
       all_list{'premises; premise. Provable{'logic; derivation_goal{'premise}}};
       all_list{'premises; premise. (all w: 'ty. (('A['w] = derivation_goal{'premise} in BTerm) => 'C['w]))}
       >- 'C['u] }-->
   sequent { <H>; v: 'ty; x: Provable{'logic; 'A['v]}; <J['v; 'x]> >- 'C['v] }

interactive provable_elim1 'H :
   [wf] sequent { <H>; v: 'ty; x: Provable{'logic; 'A['v]}; <J['v; 'x]> >- 'logic in Logic } -->
   [wf] sequent { <H>; v: 'ty; x: Provable{'logic; 'A['v]}; <J['v; 'x]>; w: 'ty >- 'A['w] in BTerm } -->
   sequent { <H>; v: 'ty; x: Provable{'logic; 'A['v]}; <J['v; 'x]>;
       u: 'ty;
       premises: list{BTerm};
       witness: ProofStepWitness;
       SimpleStep{'premises; 'A['u]; 'witness; 'logic};
       all_list{'premises; premise. Provable{'logic; 'premise}};
       all_list{'premises; premise. (all w: 'ty. (('A['w] = 'premise in BTerm) => 'C['w]))}
       >- 'C['u] }-->
   sequent { <H>; v: 'ty; x: Provable{'logic; 'A['v]}; <J['v; 'x]> >- 'C['v] }

interactive provableSequent_elim 'H :
   [wf] sequent { <H>; v: 'ty; x: ProvableSequent{'logic; 'A['v]}; <J['v; 'x]> >- 'logic in Logic } -->
   [wf] sequent { <H>; v: 'ty; x: ProvableSequent{'logic; 'A['v]}; <J['v; 'x]>; w: 'ty >- 'A['w] in BTerm } -->
   sequent { <H>; v: 'ty; x: ProvableSequent{'logic; 'A['v]}; <J['v; 'x]>;
       u: 'ty;
       premises: list{BTerm};
       witness: ProofStepWitness;
       SimpleStep{'premises; 'A['u]; 'witness; 'logic};
       all_list{'premises; premise. Provable{'logic; 'premise}};
       all_list{'premises; premise. (all w: 'ty. (('A['w] = 'premise in BTerm) => 'C['w]))}
       >- 'C['u] }-->
   sequent { <H>; v: 'ty; x: ProvableSequent{'logic; 'A['v]}; <J['v; 'x]> >- 'C['v] }

interactive step_empty_logic {| elim; nth_hyp |} 'H :
   sequent { <H>; x: SimpleStep{'assums; 'goal; 'witness; empty_logic}; <J['x]> >- 'C['x] }

interactive step_rules_logic_cons {| elim |} 'H :
   sequent { <H>; ProofCheck{'r; 'assums; 'goal; 'witness}; <J[it]> >- 'C[it] } -->
   sequent { <H>; SimpleStep{'assums; 'goal; 'witness; rules_logic{'rules; 'logic}}; <J[it]> >- 'C[it] } -->
   sequent { <H>; x: SimpleStep{'assums; 'goal; 'witness; rules_logic{cons{'r; 'rules}; 'logic}}; <J['x]> >- 'C['x] }

interactive step_rules_logic_nil {| elim |} 'H :
   sequent { <H>; SimpleStep{'assums; 'goal; 'witness; 'logic}; <J[it]> >- 'C[it] } -->
   sequent { <H>; x: SimpleStep{'assums; 'goal; 'witness; rules_logic{nil; 'logic}}; <J['x]> >- 'C['x] }

(*
 * XXX TODO: (2006/02/25 nogin)
 * The "'logic_2 in Logic" condition is unnecessary, but getting rid of it is hard (will require "l1
 * in A List && l1 @ l2 in A List >- l2 in A List" lemma). Leaving it in for now.
 *)
interactive step_union_logic_elim {| elim |} 'H :
   [wf] sequent { <H>; x: SimpleStep{'assums; 'goal; 'witness; union_logic{'logic_1; 'logic_2}}; <J['x]> >-
      'logic_1 in Logic } -->
   [wf] sequent { <H>; x: SimpleStep{'assums; 'goal; 'witness; union_logic{'logic_1; 'logic_2}}; <J['x]> >-
      'logic_2 in Logic } -->
   sequent { <H>; SimpleStep{'assums; 'goal; 'witness; 'logic_1}; <J[it]> >- 'C[it] } -->
   sequent { <H>; SimpleStep{'assums; 'goal; 'witness; 'logic_2}; <J[it]> >- 'C[it] } -->
   sequent { <H>; x: SimpleStep{'assums; 'goal; 'witness; union_logic{'logic_1; 'logic_2}}; <J['x]> >- 'C['x] }

(************************************************************************
 * IsJudgment.
 *)
doc <:doc<
   Prove << IsJudgment{'logic; 'seq} >> with sublogic.
>>
interactive provable_sub 'logic1 : <:xrule<
   "wf" : <H> >- logic1 in Logic -->
   "wf" : <H> >- logic2 in Logic -->
   <H> >- SubLogic{logic1; logic2} -->
   <H> >- Provable{logic1; seq} -->
   <H> >- Provable{logic2; seq}
>>

interactive is_judgment_sub 'logic1 : <:xrule<
   "wf" : <H> >- logic1 in Logic -->
   "wf" : <H> >- logic2 in Logic -->
   <H> >- SubLogic{logic1; logic2} -->
   <H> >- IsJudgment{logic1; seq} -->
   <H> >- IsJudgment{logic2; seq}
>>

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
