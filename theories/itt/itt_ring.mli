(*
 * Groups.
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
 * Copyright (C) 2003 Yegor Bryukhov, GC CUNY
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
 * Email : ybryukhov@gc.cuny.edu
 *)

extends Itt_group

open Tactic_type.Conversionals

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare agroup[i:l]
declare aabelg[i:l]

declare prering[i:l]
declare isDistrib{'R}
declare ring[i:l]
declare Z

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval unfold_prering : conv
topval unfold_isDistrib : conv
topval unfold_ring : conv
topval unfoldZ : conv

topval fold_prering1 : conv
topval fold_prering : conv
topval fold_isDistrib1 : conv
topval fold_isDistrib : conv
topval fold_ring1 : conv
topval fold_ring : conv
topval foldZ : conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
