(*
 * Type for a Geometric Algebra.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2017 Jason Hickey
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
 * @email{jasonh@gmail.com}
 * @end[license]
 *)
doc <:doc< @parents >>
extends Itt_theory
doc docoff

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp

doc <:doc<
     @terms

     The @tt{gatype} defines the domain of an algebra.
>>
declare gatype{'T}

doc docoff

let gatype_term = << "gatype"{'t} >>
let gatype_opname = opname_of_term gatype_term
let is_gatype_term = is_dep0_term gatype_opname
let mk_gatype_term = mk_dep0_term gatype_opname
let dest_gatype_term = dest_dep0_term gatype_opname

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
