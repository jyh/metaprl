doc <:doc<
   More list operations.

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2005 Mojave Group, Caltech

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
   @end[license]

   @parents
>>
extends Itt_list2

open Basic_tactics

(*
 * The type containing nil
 *)
declare Nil

(*
 * The type containing << cons{'e1; 'e2} >> for any << 'e1 >> and
 * << 'e2 >>.
 *)
declare Cons

(*
 * The type of conses that are nested correctly for depth << 'n >>.
 *)
declare Cons{'n}

(*
 * The type of lambda-expressions producing cons's.
 *)
declare ConsFun
declare ConsFun{'n}

(*
 * Prefix and suffix operations.
 *)
declare nth_prefix{'l; 'i}
declare nth_suffix{'l; 'i}

(************************************************************************
 * Tactics.
 *)
topval fold_guard : conv

topval splitConsT : term -> tactic
topval splitConsFunT : term -> tactic

topval normalizeListOfFunC : conv

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
