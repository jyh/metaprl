(*
 * Define a set of precedences for use generically in
 * display forms.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003 Jason Hickey, Caltech
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
extends Base_theory

(*
 * Precedences.
 *)
prec prec_if
prec prec_shift
prec prec_and
prec prec_add
prec prec_mul
prec prec_uminus
prec prec_coerce
prec prec_apply

prec prec_shift > prec_if
prec prec_and > prec_shift
prec prec_add > prec_and
prec prec_mul > prec_add
prec prec_uminus > prec_mul
prec prec_coerce > prec_uminus
prec prec_apply > prec_coerce

prec prec_colon
prec prec_fun
prec prec_union
prec prec_exists

prec prec_fun > prec_colon
prec prec_union > prec_fun
prec prec_exists > prec_union

(*
 * Display utilities.
 *)
declare display_list[sep:s]{'l}

dform display_list_cons2_df : display_list[sep:s]{cons{'a; cons{'b; 'c}}} =
   slot{'a} slot[sep:s] display_list[sep:s]{cons{'b; 'c}}

dform display_list_cons1_df : display_list[sep:s]{cons{'a; nil}} =
   slot{'a}

dform display_list_nil_df : display_list[sep:s]{nil} =
   `""

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
