(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Test code.
 * prim rules are probably just tests for display forms.
 * interactive rules are probably testing rewrites.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Brian Emre Aydemir
 * Email:  emre@its.caltech.edu
 *)

include Mc_theory

(*************************************************************************
 * Mc_set
 *************************************************************************)

(* Display tests. *)

prim mc_set_1 'H :
   sequent ['ext] { 'H >- interval{ (-32); 21 } }
   = it

prim mc_set_2 'H :
   sequent ['ext] { 'H >- int_set{
      cons{ interval{0;0};
      cons{ interval{2;3};
      cons{ interval{12;34}; nil }}}}}
   = it

prim mc_set_3 'H :
   sequent ['ext] { 'H >- rawint_set{
      int8; val_true;
      cons{ interval{0;0};
      cons{ interval{2;3};
      cons{ interval{12;34}; nil }}}}}
   = it

(* Membership tests. *)

interactive mc_set_4 'H :
   sequent ['ext] { 'H >- bfalse } -->
   sequent ['ext] { 'H >- is_member{ 128; int_set{
      cons{ interval{0;0};
      cons{ interval{1;1};
      cons{ interval{2;3};
      cons{ interval{4;5};
      cons{ interval{6;7};
      cons{ interval{8;12};
      cons{ interval{(-12);127};
      cons{ interval{139;124};      (* bad interval bounds here *)
      cons{ interval{34;39};
      cons{ interval{50;78};
      cons{ interval{79;23}; nil }}}}}}}}}}}}}}

interactive mc_set_5 'H :
   sequent ['ext] { 'H >- btrue } -->
   sequent ['ext] { 'H >- is_member{ 128; rawint_set{
      int32; val_false;
      cons{ interval{0;0};
      cons{ interval{1;1};
      cons{ interval{2;3};
      cons{ interval{4;5};
      cons{ interval{6;7};
      cons{ interval{8;12};
      cons{ interval{(-12);127};
      cons{ interval{13;129};
      cons{ interval{34;39};
      cons{ interval{50;78};
      cons{ interval{79;23}; nil }}}}}}}}}}}}}}

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
