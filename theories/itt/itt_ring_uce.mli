(*
 * Commutative unitrings with decidable equality.
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
 * Copyright (C) 1997-2004 MetaPRL Group
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
 * Author: Xin Yu
 * Email : xiny@cs.caltech.edu
 *)

extends Itt_unitring
extends Itt_ring_e

open Tactic_type.Tactic

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare preunitringE[i:l]
declare isUnitRingCE{'f}
declare unitringCE[i:l]

declare poly_ring{'F}

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval unfold_preunitringE : conv
topval unfold_isUnitRingCE : conv
topval unfold_unitringCE : conv

topval fold_preunitringE1 : conv
topval fold_preunitringE : conv
topval fold_isUnitRingCE1 : conv
topval fold_isUnitRingCE : conv
topval fold_unitringCE1 : conv
topval fold_unitringCE : conv

topval unfold_poly_ring : conv
topval fold_poly_ring : conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
