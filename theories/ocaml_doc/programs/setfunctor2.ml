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

module type EqualSig = sig
   type t
   val equal : t -> t -> bool
end;;

module type SetSig = sig
   type t
   type elt

   val empty : t
   val mem : elt -> t -> bool
   val add : elt -> t -> t
   val find : elt -> t -> elt
end;;

module MakeSet (Equal : EqualSig) : SetSig = struct
   type elt = Equal.t
   type t = elt list

   let empty = []
   let add x l = x :: l
   let mem x l = List.exists (Equal.equal x) l
   let rec find x = function
      x' :: l when Equal.equal x x' -> x'
    | _ :: l -> find x l
    | [] -> raise Not_found
end;;

module StringCaseEqual = struct
   type t = string
   let equal s1 s2 =
      String.lowercase s1 = String.lowercase s2
end;;

module StringSet = MakeSet (StringCaseEqual);;

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
