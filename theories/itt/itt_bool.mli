(*
 * Boolean operations.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
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
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)

include Itt_equal

open Refiner.Refiner.Term
open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "bool"

declare "btrue"
declare "bfalse"
declare bor{'a; 'b}
declare band{'a; 'b}
declare bnot{'a; 'b}

declare ifthenelse{'e1; 'e2; 'e3}

(*
 * This term is used to reduce param actions.
 *)
declare "bool_flag"[@n:t]

rewrite reduceBoolTrue : "bool_flag"["true":t] <--> "btrue"
rewrite reduceBoolFalse : "bool_flag"["false":t] <--> "bfalse"

(*
 * Reduction.
 *)
rewrite reduceIfthenelseTrue : ifthenelse{btrue; 'e1; 'e2} <--> 'e1
rewrite reduceIfthenelseFalse : ifthenelse{bfalse; 'e1; 'e2} <--> 'e2
rewrite unfoldBor : bor{'a; 'b} <--> ifthenelse{'a; btrue; 'b}
rewrite unfoldBand : band{'a; 'b} <--> ifthenelse{'a; 'b; bfalse}
rewrite unfoldBnot : bnot{'a} <--> ifthenelse{'a; bfalse; btrue}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Unit
 * by boolFormation
 *)
axiom boolFormation 'H : sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- Bool = Bool in Ui ext Ax
 * by boolEquality
 *)
axiom boolEquality 'H : sequent ['ext] { 'H >- "bool" = "bool" in univ[@i:l] }

(*
 * H >- Bool ext btrue
 * by bool_*Formation
 *)
axiom bool_trueFormation 'H : sequent ['ext] { 'H >- "bool" }
axiom bool_falseFormation 'H : sequent ['ext] { 'H >- "bool" }

(*
 * H >- Unit = Unit in Ui ext Ax
 * by boolEquality
 *)
axiom bool_trueEquality 'H : sequent ['ext] { 'H >- btrue = btrue in "bool" }
axiom bool_falseEquality 'H : sequent ['ext] { 'H >- bfalse = bfalse in "bool" }

(*
 * H; i:x:Unit; J >- C
 * by boolElimination i
 * H; i:x:Unit; J[it / x] >- C[it / x]
 *)
axiom boolElimination 'H 'J 'x :
   sequent['ext] { 'H; x: "bool"; 'J[btrue] >- 'C[btrue] } -->
   sequent['ext] { 'H; x: "bool"; 'J[bfalse] >- 'C[bfalse] } -->
   sequent ['ext] { 'H; x: "bool"; 'J['x] >- 'C['x] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_boolT : int -> tactic
val eqcd_boolT : tactic
val eqcd_btrueT : tactic
val eqcd_bfalseT : tactic
val bool_term : term
val btrue_term : term
val bfalse_term : term

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
