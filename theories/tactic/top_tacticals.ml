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

include Mptop

(*
 * Toploop values.
 *)
let idT = Tactic_type.Tacticals.idT
let cutT = Tactic_type.Tacticals.cutT
let failT = Tactic_type.Tacticals.failT
let failWithT = Tactic_type.Tacticals.failWithT
let nthAssumT = Tactic_type.Tacticals.nthAssumT
let timingT = Tactic_type.Tacticals.timingT
let completeT = Tactic_type.Tacticals.completeT
let progressT = Tactic_type.Tacticals.progressT
let repeatT = Tactic_type.Tacticals.repeatT
let repeatForT = Tactic_type.Tacticals.repeatForT
let seqOnSameConclT = Tactic_type.Tacticals.seqOnSameConclT
let prefix_orelseT = Tactic_type.Tacticals.prefix_orelseT
let prefix_andalsoT = Tactic_type.Tacticals.prefix_andalsoT
let prefix_orthenT = Tactic_type.Tacticals.prefix_orthenT
let firstT = Tactic_type.Tacticals.firstT
let tryT = Tactic_type.Tacticals.tryT
let prefix_thenT = Tactic_type.Tacticals.prefix_thenT
let prefix_thenLT = Tactic_type.Tacticals.prefix_thenLT
let prefix_then_OnFirstT = Tactic_type.Tacticals.prefix_then_OnFirstT
let prefix_then_OnLastT = Tactic_type.Tacticals.prefix_then_OnLastT
let prefix_then_OnSameConclT = Tactic_type.Tacticals.prefix_then_OnSameConclT
let addHiddenLabelT = Tactic_type.Tacticals.addHiddenLabelT
let removeHiddenLabelT = Tactic_type.Tacticals.removeHiddenLabelT
let keepingLabelT = Tactic_type.Tacticals.keepingLabelT
let ifLabT = Tactic_type.Tacticals.ifLabT
let prefix_thenMT = Tactic_type.Tacticals.prefix_thenMT
let prefix_thenMLT = Tactic_type.Tacticals.prefix_thenMLT
let prefix_thenAT = Tactic_type.Tacticals.prefix_thenAT
let prefix_thenALT = Tactic_type.Tacticals.prefix_thenALT
let prefix_thenWT = Tactic_type.Tacticals.prefix_thenWT
let prefix_thenET = Tactic_type.Tacticals.prefix_thenET
let prefix_thenPT = Tactic_type.Tacticals.prefix_thenPT
let repeatMT = Tactic_type.Tacticals.repeatMT
let repeatMForT = Tactic_type.Tacticals.repeatMForT
let seqOnMT = Tactic_type.Tacticals.seqOnMT
let seqT = Tactic_type.Tacticals.seqT
let completeMT = Tactic_type.Tacticals.completeMT
let labProgressT = Tactic_type.Tacticals.labProgressT
let onClauseT = Tactic_type.Tacticals.onClauseT
let onHypT = Tactic_type.Tacticals.onHypT
let onConclT = Tactic_type.Tacticals.onConclT
let onClausesT = Tactic_type.Tacticals.onClausesT
let onHypsT = Tactic_type.Tacticals.onHypsT
let onMClausesT = Tactic_type.Tacticals.onMClausesT
let onMHypsT = Tactic_type.Tacticals.onMHypsT
let onAllHypsT = Tactic_type.Tacticals.onAllHypsT
let onAllClausesT = Tactic_type.Tacticals.onAllClausesT
let tryOnAllHypsT = Tactic_type.Tacticals.tryOnAllHypsT
let tryOnAllClausesT = Tactic_type.Tacticals.tryOnAllClausesT
let onAllMHypsT = Tactic_type.Tacticals.onAllMHypsT
let onAllMClausesT = Tactic_type.Tacticals.onAllMClausesT
let tryOnAllMHypsT = Tactic_type.Tacticals.tryOnAllMHypsT
let tryOnAllMClausesT = Tactic_type.Tacticals.tryOnAllMClausesT
let onSomeAssumT = Tactic_type.Tacticals.onSomeAssumT
let onSomeHypT = Tactic_type.Tacticals.onSomeHypT
let onVarT = Tactic_type.Tacticals.onVarT
let withTermT = Tactic_type.Tacticals.withTermT
let withTypeT = Tactic_type.Tacticals.withTypeT
let withBoolT = Tactic_type.Tacticals.withBoolT
let withIntT = Tactic_type.Tacticals.withIntT
let withT = Tactic_type.Tacticals.withT
let withTermsT = Tactic_type.Tacticals.withTermsT
let atT = Tactic_type.Tacticals.atT
let selT = Tactic_type.Tacticals.selT
let altT = Tactic_type.Tacticals.altT
let thinningT = Tactic_type.Tacticals.thinningT

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
