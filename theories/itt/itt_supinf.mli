doc <:doc<
   @begin[doc]
   @module[Itt_supinf]

   SupInf decision procedure (eventually it'll become a true tactic).

   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

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

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>
(*extends Itt_equal
extends Itt_squash
extends Itt_rfun
extends Itt_bool
extends Itt_logic
extends Itt_struct
extends Itt_decidable
extends Itt_quotient
extends Itt_int_arith*)
doc <:doc< @docoff >>

open Basic_tactics
open Tactic_type.Tactic

topval coreT : tactic

topval ge2leftMinT : int -> int -> tactic
topval ge2rightMaxT : int -> int -> tactic
topval ge2transitiveT : int -> int -> tactic
topval ge_addMono2T : int -> int -> tactic
topval extract2leftC : term -> conv
topval extract2rightC : term -> conv
topval ge_normC : conv
topval core2T : tactic

topval ge_int2ratT : int -> tactic
topval preT : tactic
topval supinfT : tactic

doc <:doc< @docoff >>
