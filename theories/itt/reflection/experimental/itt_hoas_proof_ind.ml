extends Itt_hoas_proof1

open Dform
open Basic_tactics

interactive provable_elim 'H :
   [wf] sequent { <H>; <J> >- 'ty Type } -->
   [wf] sequent { <H>; <J> >- 'logic in Logic } -->
   [wf] sequent { <H>; <J>; v: 'ty >- 'A['v] in BTerm } -->
   sequent { <H>; v: 'ty; <J>;
       premises: list{Derivation{'logic}};
       goal: BTerm;
       witness: ProofStepWitness;
       ValidStep{'premises; 'goal; 'witness; 'logic};
       'A['v] = 'goal in BTerm;
       all_list{'premises; premise. (Provable{'logic; derivation_goal{'premise}} &
                    all w: 'ty. (('A['w] = derivation_goal{'premise} in BTerm) => 'C['w]))}
       >- 'C['v] }-->
   sequent { <H>; v: 'ty; Provable{'logic; 'A['v]}; <J> >- 'C['v] }

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
