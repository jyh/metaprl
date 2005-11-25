(*
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
extends Base_theory

open Basic_tactics

open Base_meta

(*
 * Translate an assumption number.
 *)
let get_pos_assum_num i assums =
   let len = List.length assums in
   let i =
      if i < 0 then
         len - i + 1
      else
         i
   in
      if i < 1 || i > len then
         raise (RefineError ("get_nth_assum", StringIntError ("assumption number is out of range", i)));
      i

let get_pos_assum_from_params params assums =
   let i =
      match params with
         t :: _ ->
            dest_meta_num t
       | [] ->
            raise (RefineError ("move_to_goal_code", StringError "no arguments"))
   in
      get_pos_assum_num i assums

let nth_assum assums i =
   List.nth assums (i - 1)

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
