(*
 * Define a custom list_of_fun for normalization purposes.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2005 Mojave Group, Caltech
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
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
extends Itt_list3
extends Itt_hoas_vector

open Basic_tactics

(************************************************************************
 * Tactics.
 *)
resource (term * conv, conv) normalize_lof

val process_normalize_lof_resource_rw_annotation : (prim_rewrite, term * conv) rw_annotation_processor

topval normalizeLofTopC : conv
topval normalizeLofC : conv
topval normalizeLofT : tactic

resource (term * conv, conv) reduce_lof

val process_reduce_lof_resource_rw_annotation : (prim_rewrite, term * conv) rw_annotation_processor

topval reduceLofTopC : conv
topval reduceLofC : conv
topval reduceLofT : tactic

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
