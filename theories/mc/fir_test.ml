(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Contains test theorems and programs.
 *)

include Mc_theory

(*
 * The term to represent I don't know what should go in a spot,
 * but it doesn't really matter anyways.
 *)
declare darb
dform darb_df : except_mode[src] :: darb = `"Darb"

(*
 * Tests.
 *)

interactive test1 'H :
   sequent ['ext] { 'H >- 20 } -->
   sequent ['ext] { 'H >-
      apply{ apply{ fix{ g. lambda{ f.
         ifthenelse{ eq_atom{ 'f; token["who":t] };
            20;
            lambda{ x. ifthenelse{ beq_int{'x;50};
               apply{ 'g; token["who":t] }; it } } } } }; token["splat":t] };
   20 } }

interactive test2 'H :
   sequent ['ext] { 'H >- 20 } -->
   sequent ['ext] { 'H >-
      apply{ apply{ fix{ g. lambda{ f.
         ifthenelse{ eq_atom{ 'f; token["who":t] };
            20;
            lambda{ x. ifthenelse{ beq_int{'x;50};
               apply{ 'g; token["who":t] }; it } } } } }; token["splat":t] };
   50 } }

