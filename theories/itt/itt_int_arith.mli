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

open Tactic_type
open Tactic_type.Conversionals

open Mp_resource
open Refiner.Refiner.Term
open Refiner.Refiner.Rewrite
open Dtactic
open Term_match_table

type ge_elim_type = int -> tactic_arg -> (term list * (int -> tactic))
type ge_intro_type = tactic_arg -> (term list * tactic)

(*val extract_ge_elim_data : (int -> tactic) term_map_table -> int -> tactic_arg -> ((term list) * (int -> tactic))*)

resource (term * (term list) * (int -> tactic), ge_elim_type) ge_elim
resource (term * (term list) * tactic, ge_intro_type) ge_intro

(*val process_ge_elim_resource_annotation :
   (Tactic.pre_tactic, term * (term list) * (int -> tactic)) annotation_processor
*)
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
topval normalizeC : conv

topval arithT : tactic

(*
 * this tactic generates an artificial example used in testn
 *)
topval genT : term list -> int -> int -> int -> int -> int -> tactic

(* sometimes these parts of arithT are useful to figure out why arithT does not work
*)
topval neqInConcl2HypT : tactic
topval arithRelInConcl2HypT : tactic
topval negativeHyp2ConclT : int -> tactic
topval findContradRelT : tactic
topval reduceContradRelT : int -> tactic
(**)
(*
topval testT : int -> tactic
topval conv2geT : int -> tactic
topval all2geT : tactic
*)
