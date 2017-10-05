(*
 * Addition in Geometric Algebra.
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

extends Ga_type
doc docoff

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp

doc <:doc<
     @terms

     The @tt{sum} term expresses addition.
>>
declare sum{'e1; 'e2}

(*
 * Equality.
 *)
prim sumEquality :
   [wf] sequent { <H> >- gatype{'T} } -->
   [wf] sequent { <H> >- 'e1 = 'e1 in 'T } -->
   [wf] sequent { <H> >- 'e2 = 'e2 in 'T } -->
   sequent { <H> >- sum{'e1; 'e2} in 'T } =
   it

doc docoff

let sum_term = << sum{'e1; 'e2} >>
let sum_opname = opname_of_term sum_term
let is_sum_term = is_dep0_dep0_term sum_opname
let dest_sum = dest_dep0_dep0_term sum_opname
let mk_sum_term = mk_dep0_dep0_term sum_opname

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
