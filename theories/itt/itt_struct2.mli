(*
 * More structural rules.
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
 * Author: Alexei Kopylov
 * kopylov@cs.cornell.edu
 *
 *)

extends Itt_struct

open Refiner.Refiner.Term

open Tactic_type.Tacticals
open Tactic_type.Sequent

topval substConclT : term -> tactic
topval substT : term -> int -> tactic
topval hypSubstT : int -> int -> tactic
topval revHypSubstT : int -> int -> tactic

topval letT : term -> tactic

topval assertEqT  : term -> tactic

topval assertSquashT  : term -> tactic
topval assertSquashAtT  : int -> term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
