(*
 * Prove simple systems of inequalities
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
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
extends Itt_logic
extends Itt_bool
extends Itt_int_ext

open Basic_tactics
open Tactic_type.Tactic

type ge_elim_type = int -> tactic_arg -> (term list * (int -> tactic))
type ge_intro_type = tactic_arg -> (term list * tactic)

resource (term * (term list) * ((term -> bool) list * (int -> tactic)), ge_elim_type) ge_elim
resource (term * (term list) * tactic, ge_intro_type) ge_intro

val process_ge_elim_resource_annotation :
   options: (term -> bool) list -> (term * (term list) * ((term -> bool) list * (int -> tactic))) annotation_processor

val process_ge_intro_resource_annotation :
   (term * (term list) * tactic) annotation_processor

val not_member : term -> bool

(*
val all2ge : tactic_arg -> (term list list * tactic) list

val prefix : 'a -> ('a list list) -> ('a list list)
val product : ('a list list) -> ('a list list) -> ('a list list)
val list_product : ('a list list list) -> ('a list list)

val all2ge_flat : tactic_arg -> term list * tactic
*)
(* Parts of normalizeC, use for debugging
topval sub_elimC : conv
topval mul_normalizeC : conv
topval add_normalizeC : conv
topval injectCoefC : conv
topval mul_BubbleSortC : conv
topval mul_BubbleStep2C : conv

topval sum_same_products1C : conv
topval sum_same_products2C : conv
topval sum_same_products3C : conv
topval sum_same_products4C : conv
*)

rewrite sub_elim_rw :
   ( 'a in int ) -->
   ( 'b in int ) -->
   ('a -@ 'b ) <--> ('a +@ ((-1) *@ 'b))

rewrite ge_addMono2_rw 'c :
   ( 'a in int ) -->
   ( 'b in int ) -->
   ( 'c in int ) -->
   ('a >= 'b) <--> (('c +@ 'a) >= ('c +@ 'b))

topval ge_addMono2C : term -> conv

topval normalizeC : conv

topval preT : tactic
topval preArithT : tactic
topval reduceContradRelT : int -> tactic
topval arithT : tactic
(*
 * Specific phases of arithT - useful for debugging arithT
 *)
topval arithRelInConcl2HypT : tactic
topval findContradRelT : tactic
(**)
topval hyp2geT : int -> tactic
topval all2geT : tactic
(*
topval testT : int -> tactic
topval conv2geT : int -> tactic
*)
