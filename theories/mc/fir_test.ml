(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Contains test theorems and programs. Some (lots) of these are
 * not intended to make a whole lot of sense.
 *)

include Base_theory
include Itt_theory
include Fir_int_set
include Fir_ty
include Fir_exp
include Fir_int

(*************************************************************************
 * Simple program tests.
 * Should be provable with rw reduceC 0 thenT trivialT.
 * (Though what we're "proving" probably makes little sense.)
 *************************************************************************)

(*
interactive prog0 'H :
   sequent ['ext] { 'H >- 3 } -->
   sequent ['ext] { 'H >-
      letAlloc{ allocTuple{ cons{ 2; nil } }; ar1.
      letAlloc{ allocArray{ copy{ 5; 4 } }; ar2.
      letSubscript{ 'ar1; 0; s1.
      letSubscript{ 'ar2; 3; s2.
      binOp{ ltIntOp; 's1; 's2; comp.
      "match"{ 'comp;
         cons{ matchCase{ftrueSet; 3}; cons{ matchCase{ffalseSet; 4}; nil } }
      }}}}}}}
*)

(*************************************************************************
 * Silly trivial tests for debugging purposes.
 *************************************************************************)

(* Set debugging. *)
interactive set0 'H :
   sequent ['ext] { 'H >- btrue } -->
   sequent ['ext] { 'H >- "match"{ 2;
   cons{ matchCase{ int_set{cons{interval{3; 12};nil}}; bfalse };
         cons{ matchCase{ int_set{cons{interval{(-10); (-4)};
            cons{interval{ 1; 2 };nil}}}; btrue };
               nil
         }
   }}}
