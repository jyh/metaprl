(*
 * prod is the basic operator of Geometric Algebra.
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
extends Ga_sum
doc docoff

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp

doc <:doc<
     @terms

     The @tt{prod} term is basic operator, the product.
>>
declare prod{'e1; 'e2}

(*
 * Equality.
 *)
prim sumEquality :
   [wf] sequent { <H> >- gatype{'T} } -->
   [wf] sequent { <H> >- 'e1 = 'e1 in 'T } -->
   [wf] sequent { <H> >- 'e2 = 'e2 in 'T } -->
   sequent { <H> >- prod{'e1; 'e2} in 'T } =
   it

prim assoc :
   [wf] sequent { <H> >- gatype{'T} } -->
   [wf] sequent { <H> >- 'e1 = 'e1 in 'T } -->
   [wf] sequent { <H> >- 'e2 = 'e2 in 'T } -->
   [wf] sequent { <H> >- 'e3 = 'e3 in 'T } -->
   sequent { <H> >- prod{'e1; prod{'e2; 'e3}} = prod{prod{'e1; 'e2}; 'e3} in 'T } =
   it

prim distrib :
   [wf] sequent { <H> >- gatype{'T} } -->
   [wf] sequent { <H> >- 'e1 = 'e1 in 'T } -->
   [wf] sequent { <H> >- 'e2 = 'e2 in 'T } -->
   [wf] sequent { <H> >- 'e3 = 'e3 in 'T } -->
   sequent { <H> >- prod{'e1; sum{'e2; 'e3}} = sum{prod{'e1; 'e2}; prod{'e1; 'e3}} in 'T } =
   it

doc docoff

let prod_term = << prod{'e1; 'e2} >>
let prod_opname = opname_of_term prod_term
let is_prod_term = is_dep0_dep0_term prod_opname
let dest_prod = dest_dep0_dep0_term prod_opname
let mk_prod_term = mk_dep0_dep0_term prod_opname

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
