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
 * Should be provable with rw reduceC 0 thenT autoT.
 *************************************************************************)

(* dummy term... hehe *)
declare darb
dform darb_df : darb = `"darb"

(* Integer tests... for sanity. *)
interactive int1 'H :
   sequent ['ext] { 'H >- 1 } -->
   sequent ['ext] { 'H >- binOp{ plusIntOp; 0; 1; v. 'v } }
interactive int2 'H :
   sequent ['ext] { 'H >- 1 } -->
   sequent ['ext] { 'H >- binOp{ minusIntOp; 2; 1; v. 'v } }
interactive int3 'H :
   sequent ['ext] { 'H >- 0 } -->
   sequent ['ext] { 'H >- binOp{ mulIntOp; 0; 1; v. 'v } }
interactive int4 'H :
   sequent ['ext] { 'H >- 1 } -->
   sequent ['ext] { 'H >- binOp{ divIntOp; 6; 4; v. 'v } }
interactive int5 'H :
   sequent ['ext] { 'H >- 1 } -->
   sequent ['ext] { 'H >- binOp{ remIntOp; 5; 4; v. 'v } }
interactive int6 'H :
   sequent ['ext] { 'H >- 1 } -->
   sequent ['ext] { 'H >- unOp{ uminusIntOp; (-1); v. 'v } }
interactive int7 'H :
   sequent ['ext] { 'H >- 0 } -->
   sequent ['ext] { 'H >- binOp{ eqIntOp; 0; 1; v. 'v } }
interactive int8 'H :
   sequent ['ext] { 'H >- 1 } -->
   sequent ['ext] { 'H >- binOp{ neqIntOp; 0; 1; v. 'v } }
interactive int9 'H :
   sequent ['ext] { 'H >- 0 } -->
   sequent ['ext] { 'H >- binOp{ ltIntOp; 1; 1; v. 'v } }
interactive int10 'H :
   sequent ['ext] { 'H >- 1 } -->
   sequent ['ext] { 'H >- binOp{ leIntOp; 0; 1; v. 'v } }
interactive int11 'H :
   sequent ['ext] { 'H >- 1 } -->
   sequent ['ext] { 'H >- binOp{ leIntOp; 1; 1; v. 'v } }
interactive int12 'H :
   sequent ['ext] { 'H >- 0 } -->
   sequent ['ext] { 'H >- binOp{ gtIntOp; 0; 1; v. 'v } }
interactive int13 'H :
   sequent ['ext] { 'H >- 0 } -->
   sequent ['ext] { 'H >- binOp{ geIntOp; 0; 1; v. 'v } }
interactive int14 'H :
   sequent ['ext] { 'H >- 1 } -->
   sequent ['ext] { 'H >- binOp{ geIntOp; 1; 1; v. 'v } }

(* Identity test. *)
interactive id 'H :
   sequent ['ext] { 'H >- 32 } -->
   sequent ['ext] { 'H >- unOp{ idOp; 32; v. 'v } }

(* Alloc tests. *)
interactive alloc1 'H :
   sequent ['ext] { 'H >- ref{0} } -->
   sequent ['ext] { 'H >-
      prog{empty; letAlloc{allocTuple{darb; cons{1; nil}}; v.
         value{ 'v } } } }
interactive alloc2 'H :
   sequent ['ext] { 'H >- ref{0} } -->
   sequent ['ext] { 'H >-
      prog{empty; letAlloc{allocArray{darb; cons{2; cons{1; nil}}}; v.
         value{ 'v } }}}
interactive alloc3 'H :
   sequent ['ext] { 'H >- ref{1} } -->
   sequent ['ext] { 'H >- prog{ empty;
      letAlloc{ allocArray{darb; cons{2;nil}}; v.
      letAlloc{ allocArray{darb; cons{3;nil}}; e.
      value{ 'e } } } } }
interactive alloc4 'H :
   sequent ['ext] { 'H >- prog{
      pair{ 4; cons{ block{0;cons{2;nil}};
               cons{ block{0;cons{3;nil}};
               cons{ block{0;cons{4;nil}};
               cons{ block{0;cons{5;nil}}; nil }}}} };
      ref{3} } } -->
   sequent ['ext] { 'H >- prog{ empty;
      letAlloc{ allocTuple{darb; cons{5;nil}}; a1.
      letAlloc{ allocArray{darb; cons{4;nil}}; a2.
      letAlloc{ allocTuple{darb; cons{3;nil}}; a3.
      letAlloc{ allocTuple{darb; cons{2;nil}}; a4. 'a4 }}}}}}

(* Match tests. *)
interactive match1 'H :
   sequent ['ext] { 'H >- 512 } -->
   sequent ['ext] { 'H >- "match"{ 32;
      cons{matchCase{int_set{1;31};2};
      cons{matchCase{int_set{25;35};512};nil}}}}
interactive match2 'H :
   sequent ['ext] { 'H >- 317 } -->
   sequent ['ext] { 'H >- "match"{ block{ 2; nil };
      cons{matchCase{int_set{1;31};317};
      cons{matchCase{int_set{25;35};512};nil}}}}
interactive match3 'H :
   sequent ['ext] { 'H >- "match"{ 3; nil } } -->
   sequent ['ext] { 'H >- "match"{ 3;
      cons{matchCase{true_set;1}; cons{matchCase{false_set;0}; nil}}}}

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
interactive sub3 'H :
   sequent ['ext] { 'H >- 6 } -->
   sequent ['ext] { 'H >- prog{ empty;
      letAlloc{ allocTuple{darb; cons{1; cons{2; cons{3; nil}}}}; a1.
      letAlloc{ allocArray{darb; cons{4; cons{5; nil}}}; a2.
      letAlloc{ allocTuple{darb; cons{6; nil}}; a3.
      setSubscript{ 'a2; 1; 6;
      letSubscript{ 'a2; 1; v. value{ 'v } }}}}}}}

(*************************************************************************
 * Complex program tests.
 * Should be provable with rw reduceC 0 thenT autoT.
 *************************************************************************)

interactive complex1 'H :
   sequent ['ext] { 'H >- 128 } -->
   sequent ['ext] { 'H >-
      prog{ empty;
         letAlloc{ allocArray{darb; cons{1;cons{2;cons{3;nil}}}}; a1.
         letAlloc{ allocTuple{darb; cons{4;cons{5;cons{6;nil}}}}; a2.
         letAlloc{ allocTuple{darb; cons{0;cons{9;cons{0;nil}}}}; a3.
         letAlloc{ allocTuple{darb; cons{8;cons{8;cons{8;nil}}}}; a4.
         setSubscript{ 'a1; 1; 20;
         setSubscript{ 'a2; 0; (-40);
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

interactive complex2 'H :
   sequent ['ext] { 'H >- 6 } -->
   sequent ['ext] { 'H >- prog{ empty;
      letAlloc{ allocArray{darb; cons{0;nil}}; a1.
      setSubscript{ 'a1; 0; 1;
      letSubscript{ 'a1; 0; v.
      binOp{ plusIntOp; 'v; 2; e.
      setSubscript{ 'a1; 0; 'e;
      letSubscript{ 'a1; 0; v2.
      binOp{ plusIntOp; 'v2; 3; e. value{ 'e }}}}}}}}}}
