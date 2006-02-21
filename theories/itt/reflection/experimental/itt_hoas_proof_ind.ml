extends Itt_hoas_proof
extends Itt_hoas_sequent_bterm
extends Itt_hoas_sequent_proof

open Dform
open Basic_tactics

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

interactive provableSequent_elim 'H :
   [wf] sequent { <H>; v: 'ty; x: ProvableSequent{'logic; 'A['v]}; <J['v; 'x]> >- 'logic in Logic } -->
   [wf] sequent { <H>; v: 'ty; x: ProvableSequent{'logic; 'A['v]}; <J['v; 'x]>; w: 'ty >- 'A['w] in BSequent } -->
   sequent { <H>; v: 'ty; x: ProvableSequent{'logic; 'A['v]}; <J['v; 'x]>;
       u: 'ty;
       premises: list{Derivation{'logic}};
       witness: ProofStepWitness;
       ValidStep{'premises; 'A['u]; 'witness; 'logic};
       all_list{'premises; premise. (Provable{'logic; derivation_goal{'premise}} &
                    all w: 'ty. (('A['w] = derivation_goal{'premise} in BTerm) => 'C['w]))}
       >- 'C['u] }-->
   sequent { <H>; v: 'ty; x: ProvableSequent{'logic; 'A['v]}; <J['v; 'x]> >- 'C['v] }

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

interactive provableSequent_elim1 'H :
   [wf] sequent { <H>; v: 'ty; x: ProvableSequent{'logic; 'A['v]}; <J['v; 'x]> >- 'logic in Logic } -->
   [wf] sequent { <H>; v: 'ty; x: ProvableSequent{'logic; 'A['v]}; <J['v; 'x]>; w: 'ty >- 'A['w] in BSequent } -->
   sequent { <H>; v: 'ty; x: ProvableSequent{'logic; 'A['v]}; <J['v; 'x]>;
       u: 'ty;
       premises: list{BSequent};
       witness: ProofStepWitness;
       SimpleStep{'premises; 'A['u]; 'witness; 'logic};
       (*'A['u] = ...some bsequent ... in BTerm
       ProvableSequent{'logic; 'A['u]}*)
       all_list{'premises; premise. (ProvableSequent{'logic; 'premise} &
                    all w: 'ty. (('A['w] = 'premise in BTerm) => 'C['w]))}
       >- 'C['u] }-->
   sequent { <H>; v: 'ty; x: ProvableSequent{'logic; 'A['v]}; <J['v; 'x]> >- 'C['v] }
