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
extends Itt_hoas_bterm

open Basic_tactics

(************************************************************************
 * Terms.
 *)
declare lof{i. 'f['i]; 'n}

declare lof_nth{'x; 'i}

declare lof_bind{'n; x. 'e['x]}

(************************************************************************
 * Resources.
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

(************************************************************************
 * Tactics.
 *)
val bind_to_lof_bind : conv
val bindn_to_lof_bind : conv
val coalesce_lof_bind : conv
val substl_substl_lof2 : conv
val reduce_lof_bind_mk_bterm : conv
topval fold_lof_bind : conv

topval lofBindElimC : conv

(************************************************************************
 * Terms.
 *)
val is_lof_bind_term : term -> bool
val mk_lof_bind_term : var -> term -> term -> term
val dest_lof_bind_term : term -> var * term * term

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
