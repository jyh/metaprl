(*
 * Interval sets for integers, rawints, and floats.
 * For us, and interval-set is a list of intervals.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2002 Jason Hickey, Caltech
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
extends M_prec

(*
 * An interval has two bounds, and a set is just
 * a list of intervals.
 *)
declare closed{'i}
declare "open"{'i}
declare interval{'lower; 'upper}

(*
 * The intervals are in a list.
 *)
declare IntSet
declare RawIntSet
declare interval_set{'kind; 'intervals}

(*
 * Display.
 *)
declare left{'i}
declare right{'i}

dform left_closed_df : left{closed{'i}} =
   `"[" slot{'i}

dform left_open_df : left{."open"{'i}} =
   `"(" slot{'i}

dform right_closed_df : right{closed{'i}} =
   slot{'i} `"]"

dform right_open_df : right{."open"{'i}} =
   slot{'i} `")"

dform interval_df : interval{'lower; 'upper} =
   left{'lower} `".." right{'upper}

(*
 * Interval sets.
 *)
declare interval_list{'intervals}

dform int_set_df : IntSet =
   bf["IntSet"]

dform raw_int_set_df : RawIntSet =
   bf["RawIntSet"]

dform interval_set_df : interval_set{'kind; 'intervals} =
   szone pushm[0] pushm[3] slot{'kind} `"{ " interval_list{'intervals} popm hspace `"}" popm ezone

dform interval_list_cons_df1 : interval_list{cons{'a; cons{'b; 'c}}} =
   slot{'a} `"," hspace interval_list{cons{'b; 'c}}

dform interval_list_cons_df2 : interval_list{cons{'a; nil}} =
   slot{'a}

dform interval_list_nil_df : interval_list{nil} =
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
