(*
 * Simple finite functions.
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
extends Itt_nat
extends Itt_match
extends Itt_int_arith
extends Itt_omega

open Basic_tactics

(************************************************************************
 * Definitions.
 *)
define unfold_simple_ffun : simple_ffun{'T} <--> <:itt<
   Prod n: int * ({ 0..n- } -> T)
>>

define unfold_length_ffun : length_ffun{'f} <-->
   fst{'f}

define unfold_apply_ffun : apply_ffun{'f; 'i} <-->
   snd{'f} 'i

define unfold_add_ffun : add_ffun{'f; 'x} <--> <:itt<
   let len, g = f in
      len +@ 1, (fun i -> if i ==b len then x else g i)
>>

(************************************************************************
 * Display.
 *)
dform simple_ffun_df : simple_ffun{'T} =
   `"sff(" slot{'T} `")"

dform length_ffun_df : length_ffun{'f} =
   `"sff|" slot{'f} `"|"

dform apply_ffun_df : apply_ffun{'f; 'i} =
   `"sff(" slot{'f} `" @ " slot{'i} `")"

dform add_ffun_df : add_ffun{'f; 'x} =
   `"sff(" slot{'f} `" += " slot{'x} `")"

(************************************************************************
 * Well-formedness.
 *)
interactive simple_ffun_univ {| intro [] |} : <:itt_rule<
    <H> >- T IN << univ[i:l] >> -->
    <H> >- sff T IN << univ[i:l] >>
>>

interactive simple_ffun_wf {| intro [] |} : <:itt_rule<
    <H> >- T type -->
    <H> >- (sff T) type
>>

interactive length_ffun_wf {| intro [intro_typeinf << 'f >>] |} simple_ffun{'T} : <:itt_rule<
    <H> >- T type -->
    <H> >- f IN sff T -->
    <H> >- sff |f| IN int
>>

interactive apply_ffun_wf {| intro [] |} : <:itt_rule<
    <H> >- T type -->
    <H> >- f IN sff T -->
    <H> >- i IN int -->
    <H> >- 0 <= i -->
    <H> >- i < sff |f| -->
    <H> >- sff { f @ i } IN T
>>

interactive add_ffun_wf {| intro [] |} : <:itt_rule<
   <H> >- f IN sff T -->
   <H> >- x IN T -->
   <H> >- sff { f += x } IN sff T
>>

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
