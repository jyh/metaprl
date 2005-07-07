doc <:doc<
   @module[Itt_supinf]

   SupInf decision procedure (eventually it'll become a true tactic).


   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998 Jason Hickey, Cornell University

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

   Author: Yegor Bryukhov
   @email{ybryukhov@gc.cuny.edu}
   @end[license]
>>

open Basic_tactics
open Tactic_type.Tactic

topval ge2transitiveT : int -> int -> tactic
topval ge_addMono2T : int -> int -> tactic
topval extract2leftC : term -> conv
topval extract2rightC : term -> conv
topval ge_normC : conv

topval ge_int2ratT : int -> tactic
topval coreT : tactic
topval core2T : tactic
topval supinfT : tactic
