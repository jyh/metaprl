(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Contains test theorems and programs.
 *)

include Base_theory
include Itt_theory
include Fir_state
include Fir_int_set
include Fir_ty
include Fir_exp
include Fir_int

(*************************************************************************
 * Simple program tests.
 * Should be provable with rw reduceC 0 thenT trivialT.
 *************************************************************************)

(* dummy term... hehe *)
declare darb
dform darb_df : darb = `"darb"

(* Alloc tests. *)
interactive alloc1 'H :
   sequent ['ext] { 'H >-
      prog{ cons{ pair{ 0; block{ 0; cons{1; nil}} }; nil }; ref{ 0} } } -->
   sequent ['ext] { 'H >-
      prog{ empty; letAlloc{ allocTuple{darb; cons{1; nil}}; v. 'v } } }
interactive alloc2 'H :
   sequent ['ext] { 'H >-
      prog{ cons{ pair{ 0; block{0; cons{2; cons{1; nil}}} }; nil };
         ref{ 0} } } -->
   sequent ['ext] { 'H >-
      prog{empty; letAlloc{allocArray{darb; cons{2; cons{1; nil}}}; v. 'v}}}

(* Subscripting tests. *)
interactive sub1 'H :
   sequent ['ext] { 'H >- 1 } -->
   sequent ['ext] { 'H >-
      prog{ empty; letAlloc{ allocTuple{darb; cons{1; nil}}; v.
         letSubscript{ 'v; 0; w. value{'w} } } } }
interactive sub2 'H :
   sequent ['ext] { 'H >- 2 } -->
   sequent ['ext] { 'H >-
      prog{ empty; letAlloc{ allocTuple{darb; cons{1; nil}}; v.
         setSubscript{ 'v; 0; 2;
         letSubscript{ 'v; 0; w. value{ 'w } } } } } }

(*************************************************************************
 * Complex program test.
 * Should be provable with rw reduceC 0 thenT trivialT.
 *************************************************************************)

interactive complex1 'H :
   sequent ['ext] { 'H >- 512 } -->
   sequent ['ext] { 'H >-
      prog{ empty;
         letAlloc{ allocArray{darb; cons{1;cons{2;cons{3;nil}}}}; a1.
         letAlloc{ allocTuple{darb; cons{4;cons{5;cons{6;nil}}}}; a2.
         letAlloc{ allocTuple{darb; cons{0;cons{9;cons{0;nil}}}}; a3.
         letAlloc{ allocTuple{darb; cons{8;cons{8;cons{8;nil}}}}; a4.
         setSubscript{ 'a1; 1; 20;
         setSubscript{ 'a2; 0; 40;
         setSubscript{ 'a4; 2; 80;
         letSubscript{ 'a1; 1; v1.
         letSubscript{ 'a2; 0; v2.
         letSubscript{ 'a3; 2; v3.
         letSubscript{ 'a4; 2; v4.
         binOp{ plusIntOp; 'v1; 'v2; e1.
         binOp{ mulIntOp; 'v3; 'v4; e2.
         binOp{ gtIntOp; 'e1; 'e2; c.
         "match"{ 'c;
            cons{ matchCase{true_set; value{512}};
               cons{ matchCase{false_set; value{128}}; nil}}}}}}}}}}}}}}}}}}}
