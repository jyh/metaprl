(*
 * Boolean operations.
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
 * Author: Jason Hickey <jyh@cs.cornell.edu>
 * Modified by: Aleksey Nogin <nogin@cs.cornell.edu>
 *)

extends Itt_equal
extends Itt_struct
extends Itt_union
extends Itt_set
extends Itt_decidable

open Refiner.Refiner.Term
open Tactic_type.Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

prec prec_bimplies
prec prec_bor
prec prec_band
prec prec_bnot
prec prec_assert

(*
 * Definition of bool.
 *)
define unfold_bool : bool <--> (unit + unit)
define unfold_btrue : btrue <--> inl{it}
define unfold_bfalse : bfalse <--> inr{it}

define unfold_ifthenelse : ifthenelse{'b; 'e1; 'e2} <--> decide{'b; x. 'e1; y.
 'e2}
define unfold_bor : bor{'a; 'b} <--> ifthenelse{'a; btrue; 'b}
define unfold_band : band{'a; 'b} <--> ifthenelse{'a; 'b; bfalse}
define unfold_bimplies : bimplies{'a; 'b} <--> ifthenelse{'a; 'b; btrue}
define unfold_bnot : bnot{'a} <--> ifthenelse{'a; bfalse; btrue}
define unfold_assert : "assert"{'t} <--> ('t = btrue in bool)

(*
 * Reduction.
 *)
rewrite reduce_ifthenelse_true : ifthenelse{btrue; 'e1; 'e2} <--> 'e1
rewrite reduce_ifthenelse_false : ifthenelse{bfalse; 'e1; 'e2} <--> 'e2

topval fold_bool : conv
topval fold_btrue : conv
topval fold_bfalse : conv
topval fold_bor : conv
topval fold_band : conv
topval fold_bimplies : conv
topval fold_bnot : conv
topval fold_assert : conv

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Unit
 * by boolFormation
 *)
rule boolFormation : sequent { <H> >- univ[i:l] }

(*
 * H >- Bool = Bool in Ui ext Ax
 * by boolEquality
 *)
rule boolEquality : sequent { <H> >- "bool" in univ[i:l] }

(*
 * H >- Bool ext btrue
 * by bool_*Formation
 *)
rule bool_trueFormation : sequent { <H> >- "bool" }
rule bool_falseFormation : sequent { <H> >- "bool" }

rule btrue_member : sequent { <H> >- btrue in "bool" }
rule bfalse_member : sequent { <H> >- bfalse in "bool" }

(*
 * H; i:x:Unit; J >- C
 * by boolElimination i
 * H; i:x:Unit; J[it / x] >- C[it / x]
 *)
rule boolElimination2 'H :
   sequent{ <H>; <J[btrue]> >- 'C[btrue] } -->
   sequent{ <H>; <J[bfalse]> >- 'C[bfalse] } -->
   sequent { <H>; x: "bool"; <J['x]> >- 'C['x] }

(*
 * Squash elimination on assert.
 *)
rule assertSquashElim :
   sequent { <H> >- "assert"{'t} } -->
   sequent { <H> >- it in "assert"{'t} }

rule assert_bnot_intro :
   [wf] sequent { <H> >- 't1 in bool } -->
   [main] sequent { <H>; x: "assert"{'t1} >- "false" } -->
   sequent { <H> >- "assert"{bnot{'t1}} }

rule assert_bnot_elim 'H :
   [main] sequent { <H>; <J[it]> >- "assert"{'t} } -->
   sequent { <H>; x: "assert"{bnot{'t}}; <J['x]> >- 'C['x] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val is_assert_term : term -> bool
val mk_assert_term : term -> term
val dest_assert : term -> term

val bool_term : term
val btrue_term : term
val bfalse_term : term

val bor_term : term
val is_bor_term : term -> bool
val mk_bor_term : term -> term -> term
val dest_bor : term -> term * term

topval extBoolT : tactic
topval magicT : tactic
topval splitBoolT : term -> int -> tactic
topval splitITE : int -> tactic

topval reduce_bnot_bnotC : conv
topval eq_bfalse2assertT : tactic
topval assert2eq_bfalseT : tactic
topval xor_propertyC : term -> conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
