include Mc_theory

(*
 * Deadcode tests.
 *)

interactive deadcode1 'H :
   sequent ['ext] { 'H >-
      letBinop{ minusIntOp; tyInt; 2; 3; w. 'w }} -->
   sequent ['ext] { 'H >-
      letBinop{ plusIntOp; tyInt; 1; 2; v.
      letBinop{ minusIntOp; tyInt; 2; 3; w. 'w }}}

interactive deadcode2 'H :
   sequent ['ext] { 'H >- it } -->
   sequent ['ext] { 'H >-
      letBinop{ plusIntOp; tyInt; 1; 2; v.
      letBinop{ minusIntOp; tyInt; 2; 3; w. it }}}

interactive deadcode3 'H :
   sequent ['ext] { 'H >-
      letBinop{ divIntOp; 1; 2; 3; x.
      letAlloc{ allocArray{1; 2}; y.
      letSubscript{ 'x; 2; 'y; 4; h. 'h }}}} -->
   sequent ['ext] { 'H >-
      letBinop{ remIntOp; tyInt; 1; 2; a.
      letBinop{ divIntOp; 1; 2; 3; x.
      letUnop{ uminusIntOp; tyInt; 'a; b.
      letAlloc{ allocTuple{tyInt;cons{'b;nil}}; c.
      letAlloc{ allocArray{tyInt;'c}; d.
      letAlloc{ allocArray{1; 2}; y.
      letAlloc{ allocArray{tyInt;2}; e.
      letSubscript{ 1; 'x; 'y; 'e; f.
      letBinop{ 1; 2; 'f; 4; g.
      letSubscript{ 'x; 2; 'y; 4; h. 'h }}}}}}}}}}}

(*
 * Constant elimination tests.
 *)

interactive const_elim1 'H :
   sequent ['ext] { 'H >- 0 } -->
   sequent ['ext] { 'H >-
      letBinop{ plusIntOp; tyInt; atomInt{ 1 }; atomInt{ 2 }; v.
      letBinop{ minusIntOp; tyInt; 'v; atomInt{ 3 }; w. 'w }}}

interactive const_elim2 'H :
   sequent ['ext] { 'H >-
      letBinop{ plusIntOp; tyInt; 2; 'a; v. 'v }}

interactive const_elim3 'H :
   sequent ['ext] { 'H >-
      letBinop{ plusIntOp; tyInt; atomInt{4}; atomInt{6}; a.
      letBinop{ minusIntOp; tyInt; atomInt{4}; 'a; b.
      letBinop{ mulIntOp; tyInt; atomVar{'b}; atomVar{'c}; v. 'v }}}}
