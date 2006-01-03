(*
 * The @tt[Itt_vec_list1] module defines lists expressed as
 * sequents.
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
extends Meta_context_theory
extends Itt_theory

open Basic_tactics

(*
 * Normal list terms.
 *)
declare flatten{'l}

(*
 * Vector forms of lists.
 *)
declare sequent [vlist] { Term : Term >- Term } : Term
declare sequent [vflatten] { Term : Term >- Term } : Term

(*
 * ML code.
 *)
topval fold_vlist_nest : conv
topval fold_vflatten_nest : conv

topval assert_reduce_length_of_fun_term1 : term

topval reduce_length_fun_termC : conv
topval vlist_of_concrete_listC : conv

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
