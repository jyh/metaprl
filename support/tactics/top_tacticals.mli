(*
 * Some basic tacticals.
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
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)

extends Shell

open Refiner.Refiner.TermType
open Tactic_type.Tactic

(*
 * Toploop values.
 *)
topval idT : tactic
topval cutT : term -> tactic
topval failT : tactic
topval failWithT : string -> tactic
topval nthAssumT : int -> tactic
topval timingT : tactic -> tactic
topval completeT : tactic -> tactic
topval progressT : tactic -> tactic
topval whileProgressT : tactic -> tactic
topval untilFailT : tactic -> tactic
topval repeatT : tactic -> tactic
topval repeatForT : int -> tactic -> tactic
topval seqOnSameConclT : tactic list -> tactic
topval prefix_orelseT : tactic -> tactic -> tactic
topval prefix_andalsoT : tactic -> tactic -> tactic
topval prefix_orthenT : tactic -> tactic -> tactic
topval firstT : tactic list -> tactic
topval tryT : tactic -> tactic
topval prefix_thenT : tactic -> tactic -> tactic
topval prefix_thenLT : tactic -> tactic list -> tactic
topval prefix_then_OnFirstT : tactic -> tactic -> tactic
topval prefix_then_OnLastT : tactic -> tactic -> tactic
topval prefix_then_OnSameConclT : tactic -> tactic -> tactic
topval addHiddenLabelT : string -> tactic
topval removeHiddenLabelT : tactic
topval keepingLabelT : tactic -> tactic
topval ifLabT : string -> tactic -> tactic -> tactic
topval prefix_thenMT : tactic -> tactic -> tactic
topval prefix_thenMLT : tactic -> tactic list -> tactic
topval prefix_thenAT : tactic -> tactic -> tactic
topval prefix_thenALT : tactic -> tactic list -> tactic
topval prefix_thenWT : tactic -> tactic -> tactic
topval prefix_thenET : tactic -> tactic -> tactic
topval prefix_thenPT : tactic -> tactic -> tactic
topval repeatMT : tactic -> tactic
topval repeatMForT : int -> tactic -> tactic
topval whileProgressMT : tactic -> tactic
topval untilFailMT : tactic -> tactic
topval seqOnMT : tactic list -> tactic
topval seqT : tactic list -> tactic
topval completeMT : tactic -> tactic
topval labProgressT : tactic -> tactic
topval onClauseT : int -> (int -> tactic) -> tactic
topval onHypT : int -> (int -> tactic) -> tactic
topval onConclT : (int -> tactic) -> tactic
topval onClausesT : int list -> (int -> tactic) -> tactic
topval onHypsT : int list -> (int -> tactic) -> tactic
topval onMClausesT : int list -> (int -> tactic) -> tactic
topval onMHypsT : int list -> (int -> tactic) -> tactic
topval onAllHypsT : (int -> tactic) -> tactic
topval onAllClausesT : (int -> tactic) -> tactic
topval onAllAssumT : (int -> tactic) -> tactic
topval tryOnHypsT : int list -> (int -> tactic) -> tactic
topval tryOnClausesT : int list -> (int -> tactic) -> tactic
topval tryOnAllHypsT : (int -> tactic) -> tactic
topval tryOnAllClausesT : (int -> tactic) -> tactic
topval onAllMHypsT : (int -> tactic) -> tactic
topval onAllMAssumT : (int -> tactic) -> tactic
topval tryOnAllMHypsT : (int -> tactic) -> tactic
topval tryOnAllMClausesT : (int -> tactic) -> tactic
topval onSomeAssumT : (int -> tactic) -> tactic
topval onSomeHypT : (int -> tactic) -> tactic
topval withTermT : string -> term -> tactic -> tactic
topval withTypeT : string -> term -> tactic -> tactic
topval withBoolT : string -> bool -> tactic -> tactic
topval withIntT : string -> int -> tactic -> tactic
topval withT : term -> tactic -> tactic
topval withTermsT : term list -> tactic -> tactic
topval atT : term -> tactic -> tactic
topval selT : int -> tactic -> tactic
topval altT : tactic -> tactic
topval thinningT : bool -> tactic -> tactic
topval doNotThinT : tactic -> tactic

topval nameHypT : int -> string -> tactic
topval nameHypsT : int list -> string list -> tactic

val thinMatchT : (int -> int -> tactic) -> term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
