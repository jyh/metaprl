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

open Tactic_type.Conversionals

topval thenLocalMT : tactic -> tactic -> tactic
topval thenLocalMElseT : tactic -> tactic -> tactic -> tactic
topval thenLocalAT : tactic -> tactic -> tactic
topval onAllLocalMHypsT : (int -> tactic) -> tactic
topval onAllLocalMCumulativeHypsT : (int -> tactic) -> tactic

topval normalizeC : conv

topval arithT : tactic

(* sometimes these parts of arithT are useful to figure out why arithT does not work
topval arithRelInConcl2HypT : tactic
topval anyArithRel2geT : int -> tactic
topval tryReduce_geT : int -> tactic
topval findContradRelT : tactic
topval reduceContradRelT : int -> tactic
*)
