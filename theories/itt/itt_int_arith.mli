(*
 * Prove simple systems of inequalities
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
 * Author: Yegor Bryukhov
 * @email{ynb@mail.ru}
 *)

extends Itt_equal
extends Itt_rfun
extends Itt_logic
extends Itt_bool
extends Itt_int_ext

open Refiner.Refiner.Term
open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Top_conversionals
open Itt_int_ext

topval thenLocalMT : tactic -> tactic -> tactic
topval thenLocalMElseT : tactic -> tactic -> tactic -> tactic
topval thenLocalAT : tactic -> tactic -> tactic
topval onAllLocalMHypsT : (int -> tactic) -> tactic
topval onAllLocalMCumulativeHypsT : (int -> tactic) -> tactic

topval bnot_lt2geC : conv
topval ltInConcl2HypT : tactic

topval le2geT : term -> tactic
topval lt2geT : term -> tactic
topval gt2geT : term -> tactic
topval anyArithRel2geT : int -> tactic

topval arithRelInConcl2HypT : tactic
topval negativeHyp2ConclT : int -> tactic
topval ct : term -> term -> int

topval add_BubblePrimitiveC : conv
topval add_BubbleStepC : term -> conv
topval add_BubbleSortC : conv

topval add_normalizeC : conv

topval mul_BubblePrimitiveC : conv
topval mul_BubbleStepC : term -> conv
topval mul_BubbleSortC : conv

topval inject_coefC : term -> conv
topval injectCoefC : conv
topval mul_normalizeC : conv
topval open_parenthesesC : conv
topval sum_same_products1C : conv
(*
topval sum_same_products2C : conv
topval sum_same_products3C : conv
topval sum_same_products4C : conv
*)
topval same_productC : term -> conv
topval normalizeC : conv

topval ge_addContractC : conv

topval reduceContradRelT : int -> tactic

topval ge_addMono2C : term -> conv
topval reduce_geLeftC : conv
topval reduce_geRightC : conv
topval reduce_geCommonConstT : int -> tactic
topval tryReduce_geT : int -> tactic

topval sumListT : int list -> tactic
topval proveSumT : tactic

topval findContradRelT : tactic

topval arithT : tactic

(*
rule test 'a 'b 'c :
sequent [squash] { <H> >- 'a in int } -->
sequent ['ext] { <H>; x: ('a >= ('b +@ 1));
                     y: (5 in int); z: (6 in int);
                     t: ('c >= ('b +@ 3));
                     u: ('b >= ('a +@ 0))
                >- 'a >= 'c }
*)
