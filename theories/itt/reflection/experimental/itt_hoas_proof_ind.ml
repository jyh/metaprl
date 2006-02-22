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

doc rules

interactive provable_elim 'H :
   [wf] sequent { <H>; v: 'ty; x: Provable{'logic; 'A['v]}; <J['v; 'x]> >- 'logic in Logic } -->
   [wf] sequent { <H>; v: 'ty; x: Provable{'logic; 'A['v]}; <J['v; 'x]>; w: 'ty >- 'A['w] in BTerm } -->
   sequent { <H>; v: 'ty; x: Provable{'logic; 'A['v]}; <J['v; 'x]>;
       u: 'ty;
       premises: list{Derivation{'logic}};
       witness: ProofStepWitness;
       ValidStep{'premises; 'A['u]; 'witness; 'logic};
       all_list{'premises; premise. (Provable{'logic; derivation_goal{'premise}} &
                    all w: 'ty. (('A['w] = derivation_goal{'premise} in BTerm) => 'C['w]))}
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
       all_list{'premises; premise. (Provable{'logic; 'premise} &
                    all w: 'ty. (('A['w] = 'premise in BTerm) => 'C['w]))}
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
       all_list{'premises; premise. (Provable{'logic; 'premise} &
                    all w: 'ty. (('A['w] = 'premise in BTerm) => 'C['w]))}
       >- 'C['u] }-->
   sequent { <H>; v: 'ty; x: ProvableSequent{'logic; 'A['v]}; <J['v; 'x]> >- 'C['v] }

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
