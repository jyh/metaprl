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
extends Itt_finite_fun1
extends Itt_match
extends Itt_int_arith
extends Itt_omega

open Basic_tactics

(************************************************************************
 * Definitions.
 *)
define unfold_simple_ifun : simple_ifun{'T} <--> <:itt<
   "int" * ("int" -> T)
>>

define unfold_empty_ifun : empty_ifun{'x} <--> <:itt<
   0, fun y -> x
>>

define unfold_length_ifun : length_ifun{'f} <--> <:itt<
   let len, _ = f in len
>>

define unfold_apply_ifun : apply_ifun{'f; 'i} <--> <:itt<
   let _, g = f in
      g i
>>

define unfold_add_ifun : add_ifun{'f; 'x} <--> <:itt<
   let len, g = f in
      len +@ 1, (fun i -> if i ==b len then x else g i)
>>

(************************************************************************
 * Display.
 *)
dform simple_ifun_df : simple_ifun{'T} =
   `"sif(" slot{'T} `")"

dform length_ifun_df : length_ifun{'f} =
   `"sif|" slot{'f} `"|"

dform apply_ifun_df : apply_ifun{'f; 'i} =
   `"sif(" slot{'f} `" @ " slot{'i} `")"

dform add_ifun_df : add_ifun{'f; 'x} =
   `"sif(" slot{'f} `" += " slot{'x} `")"

(************************************************************************
 * Well-formedness.
 *)
interactive simple_ifun_univ {| intro [] |} : <:itt_rule<
    <H> >- T IN << univ[i:l] >> -->
    <H> >- sif T IN << univ[i:l] >>
>>

interactive simple_ifun_wf {| intro [] |} : <:itt_rule<
    <H> >- T type -->
    <H> >- (sif T) type
>>

interactive empty_ifun_wf {| intro [] |} : <:itt_rule<
    <H> >- x IN T -->
    <H> >- sif { x } IN sif T
>>

interactive length_ifun_wf {| intro [intro_typeinf << 'f >>] |} simple_ifun{'T} : <:itt_rule<
    <H> >- T Type -->
    <H> >- f IN sif T -->
    <H> >- sif |f| IN int
>>

interactive apply_ifun_wf {| intro [] |} : <:itt_rule<
    <H> >- T Type -->
    <H> >- f IN sif T -->
    <H> >- i IN "int" -->
    <H> >- sif { f @ i } IN T
>>

interactive add_ifun_wf {| intro [] |} : <:itt_rule<
   <H> >- f IN sif T -->
   <H> >- x IN T -->
   <H> >- sif { f += x } IN sif T
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
