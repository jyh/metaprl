(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Contains test theorems and programs. The trivial tests below
 * are just designed to check reduceC automation essentially and
 * aren't intended to make any other sort of sense.
 *
 * Todo:
 *    - learn how to enter in negative numbers as literals
 *      so that we can test a bit more thoroughly
 *)

include Fir_exp
include Fir_int

(*************************************************************************
 * Trivial Fir_exp tests.  They check automation and little more.
 *************************************************************************)

interactive triv_idOp 'H :
   sequent ['ext] { 'H >- 'a } -->
   sequent ['ext] { 'H >- unOp{ idOp; 'a; v. 'v } }

interactive triv_allocSafe 'H :
   sequent ['ext] { 'H >- block{ 2; cons{ 3; nil } } } -->
   sequent ['ext] { 'H >- letAlloc{ allocSafe{ 2; cons{ 3; nil } }; v. 'v } }
interactive triv_allocArray 'H :
   sequent ['ext] { 'H >- block{ 0; cons{ 4; cons{ 4; nil } } } } -->
   sequent ['ext] { 'H >- letAlloc{ allocArray{ 2; 4 }; v. 'v } }

interactive triv_match1 'H :
   sequent ['ext] { 'H >- 3 } -->
   sequent ['ext] { 'H >- "match"{0; cons{matchCase{0; 3}; nil}} }
interactive triv_match2 'H :
   sequent ['ext] { 'H >- 2 } -->
   sequent ['ext] { 'H >- "match"{ 3;
      cons{ matchCase{1; 4}; cons{matchCase{3; 2}; nil} } } }
interactive triv_match3 'H :
   sequent ['ext] { 'H >- 2 } -->
   sequent ['ext] { 'H >- "match"{ allocSafe{'tag; 'args};
      cons{ matchCase{allocArray{'len; 'init}; 1};
         cons{ matchCase{allocSafe{'tag; 'args}; 2}; nil }}}}
interactive triv_matchfails 'H :
   sequent ['ext] { 'H >- 2 } -->
   sequent ['ext] { 'H >- "match"{0;
      cons{ matchCase{ 1; 1}; cons{ matchCase{2; 2}; nil } } } }

interactive triv_letSubscript 'H :
   sequent ['ext] { 'H >- 7 } -->
   sequent ['ext] { 'H >- letSubscript{
      block{ 0; cons{ 123; cons{ 12; cons{ 7; cons{ 12; nil } } } } };
      2;
      v. 'v } }
interactive triv_letSubCheck 'H :
   sequent ['ext] { 'H >- 'a } -->
   sequent ['ext] { 'H >- letSubCheck{ 'a1; 'a2; 'a3; 'a } }

(*************************************************************************
 * Tirival Fir_int tests. They check automation and little more.
 *************************************************************************)

(* Unary operations. *)
interactive triv_uminus 'H :
   (* how do I enter in a negative number... sheesh *)
   sequent ['ext]  { 'H >- "sub"{0; 2} } -->
   sequent ['ext] { 'H >- unOp{uminusIntOp; 2; v. 'v} }

(* Basic arithmetic operations. *)
interactive triv_plus 'H :
   sequent ['ext] { 'H >- 2 } -->
   sequent ['ext] { 'H >- binOp{plusIntOp; 1; 1; v. 'v} }
interactive triv_minus 'H :
   sequent ['ext] { 'H >- 2 } -->
   sequent ['ext] { 'H >- binOp{minusIntOp; 4; 2; v. 'v} }
interactive triv_mul 'H :
   sequent ['ext] { 'H >- 4 } -->
   sequent ['ext] { 'H >- binOp{mulIntOp; 2; 2; v. 'v} }
interactive triv_div 'H :
   sequent ['ext] { 'H >- "div"{4; 2} } -->
   sequent ['ext] { 'H >- binOp{divIntOp; 4; 2; v. 'v} }
interactive triv_rem 'H :
   sequent ['ext] { 'H >- "rem"{10; 7} } -->
   sequent ['ext] { 'H >- binOp{remIntOp; 10; 7; v. 'v} }

(* Binary bitwise operators. *)
interactive triv_lsl 'H :
   sequent ['ext] { 'H >- 24 } -->
   sequent ['ext] { 'H >- binOp{ lslIntOp; 12; 1; v. 'v } }
interactive triv_lsr 'H :
   sequent ['ext] { 'H >- 1 } -->
   sequent ['ext] { 'H >- binOp{ lsrIntOp; 3; 1; v. 'v } }
interactive triv_asr 'H :
   sequent ['ext] { 'H >- 1 } -->
   sequent ['ext] { 'H >- binOp{ asrIntOp; 6; 2; v. 'v } }

(* Comparison operators. *)
interactive triv_eq 'H :
   sequent ['ext] { 'H >- btrue } -->
   sequent ['ext] { 'H >- binOp{ eqIntOp; 2; 2; v. 'v } }
interactive triv_lt 'H :
   sequent ['ext] { 'H >- btrue } -->
   sequent ['ext] { 'H >- binOp{ ltIntOp; 3; 4; v. 'v } }
interactive triv_le 'H :
   sequent ['ext] { 'H >- btrue } -->
   sequent ['ext] { 'H >- binOp{ leIntOp; 5; 5; v. 'v } }
interactive triv_gt 'H :
   sequent ['ext] { 'H >- btrue } -->
   sequent ['ext] { 'H >- binOp{ gtIntOp; 4; 3; v. 'v } }
interactive triv_ge 'H :
   sequent ['ext] { 'H >- btrue } -->
   sequent ['ext] { 'H >- binOp{ geIntOp; 1; 1; v. 'v } }

(* Exponentiation. *)
interactive triv_pow 'H :
   sequent ['ext] { 'H >- 32 } -->
   sequent ['ext] { 'H >- pow{ 2; 5 } }

(*************************************************************************
 * "Complex" tests. reduceC and autoT should still be plenty (hopefully).
 *************************************************************************)

interactive complex1 'H :
   sequent ['ext] { 'H >- 7 } -->
   sequent ['ext] { 'H >-
      letAlloc{ allocArray{ 5; 7 }; ar1.
      letSubscript{ 'ar1; 2; v. 'v
      }}}

interactive complex2 'H :
   sequent ['ext] { 'H >- 42 } -->
   sequent ['ext] { 'H >-
      letAlloc{ allocSafe{ 2; cons{ 2; nil } }; ar1.
      letAlloc{ allocArray{ 5; 4 }; ar2.
      letSubscript{ 'ar1; 0; s1.
      letSubscript{ 'ar2; 3; s2.
      binOp{ ltIntOp; 's1; 's2; comp.
      "match"{ 'comp;
         cons{ matchCase{btrue; 3}; cons{ matchCase{bfalse; 4}; nil } }
      }}}}}}}
