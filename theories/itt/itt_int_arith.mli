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

include Itt_equal
include Itt_rfun
include Itt_logic
include Itt_bool
include Itt_int_ext

open Refiner.Refiner.Term
open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Top_conversionals
open Itt_int_ext

topval add_BubblePrimitiveC : conv
topval add_BubbleStepC : term -> conv
topval add_BubbleSortC : conv

topval add_normalizeC : conv

topval ge_addContractC : conv

topval reduceContradRelT : int -> tactic

topval sumListT : int list -> tactic
topval proveSumT : tactic

topval findContradRelT : tactic

topval arithT : tactic

(*
rule test 'H 'a 'b 'c :
sequent [squash] { 'H >- 'a IN int } -->
sequent ['ext] { 'H; x: ('a >= ('b +@ 1));
                     y: (5 IN int); z: (6 IN int);
                     t: ('c >= ('b +@ 3));
                     u: ('b >= ('a +@ 0))
                >- 'a >= 'c }
*)
