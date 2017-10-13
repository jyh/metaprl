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
extends Itt_vector_space
extends Itt_labels
doc docoff

open Basic_tactics

(************************************************************************
 * Vector space
 *)

doc <:doc<
     @modsection{Geometric Algebra}

     A Geometric Algebra is a vector space with a product operator
     satisfying the axioms of a geometric algebra.

     @modsubsection{Rewrites}
>>
define unfold_pre_ga : pre_ga[i:l] <-->
   record["*:g":t]{r. 'r^vec -> 'r^vec -> 'r^vec; pre_vector_space[i:l]}

define unfold_ga_prod_is_assoc : GaProdIsAssoc{'g} <-->
   all x: 'g^vec. all y: 'g^vec. all z: 'g^vec. (('x *:g['g] ('y *:g['g] 'z)) = (('x *:g['g] 'y) *:g['g] 'z) in 'g^vec)

define unfold_ga_prod_distrib : GaProdDistrib{'g} <-->
   all x: 'g^vec. all y: 'g^vec. all z: 'g^vec. (('x *:g['g] ('y +|['g] 'z)) = (('x *:g['g] 'y) +|['g] ('x *:g['g] 'z)) in 'g^vec)

doc <:doc<
   @modsubsection{Well-formedness}

>>
interactive pre_ga_wf {| intro [] |} :
   sequent { <H> >- pre_ga[i:l] Type }

interactive pre_ga_elim {| elim [] |} 'H  :
   sequent { <H>; g: record["*:g":t]{r. 'r^vec -> 'r^vec -> 'r^vec; pre_vector_space[i:l]}; <J['g]> >- 'C['g] } -->
   sequent { <H>; g: pre_ga[i:l]; <J['g]> >- 'C['g] }

interactive ga_car_wf {| intro [intro_typeinf <<'g>>] |} pre_ga[i:l] :
   [wf] sequent { <H> >- 'g IN pre_ga[i:l] } -->
   sequent { <H> >- 'g^car Type }

interactive ga_vec_wf {| intro [intro_typeinf <<'g>>] |} pre_ga[i:l] :
   [wf] sequent { <H> >- 'g IN pre_ga[i:l] } -->
   sequent { <H> >- 'g^vec Type }

interactive ga_scalar_mul_wf {| intro [intro_typeinf <<'g>>] |} pre_ga[i:l] :
   [wf] sequent { <H> >- 'g IN pre_ga[i:l] } -->
   [wf] sequent { <H> >- 'x IN 'g^car } -->
   [wf] sequent { <H> >- 'y IN 'g^car } -->
   sequent { <H> >- 'x *['g] 'y IN 'g^car }

interactive ga_add_wf {| intro [intro_typeinf <<'g>>] |} pre_ga[i:l] :
   [wf] sequent { <H> >- 'g IN pre_ga[i:l] } -->
   [wf] sequent { <H> >- 'x IN 'g^vec } -->
   [wf] sequent { <H> >- 'y IN 'g^vec } -->
   sequent { <H> >- 'x +|['g] 'y IN 'g^vec }

interactive ga_mul_wf {| intro [intro_typeinf <<'g>>] |} pre_ga[i:l] :
   [wf] sequent { <H> >- 'g IN pre_ga[i:l] } -->
   [wf] sequent { <H> >- 'a IN 'g^car } -->
   [wf] sequent { <H> >- 'x IN 'g^vec } -->
   sequent { <H> >- 'a *|['g] 'x IN 'g^vec }

interactive ga_prod_wf {| intro [intro_typeinf <<'g>>] |} pre_ga[i:l] :
   [wf] sequent { <H> >- 'g IN pre_ga[i:l] } -->
   [wf] sequent { <H> >- 'x IN 'g^vec } -->
   [wf] sequent { <H> >- 'y IN 'g^vec } -->
   sequent { <H> >- 'x *:g['g] 'y IN 'g^vec }

interactive ga_prod_is_assoc_wf {| intro [intro_typeinf <<'g>>] |} pre_ga[i:l] :
   [wf] sequent { <H> >- 'g in pre_ga[i:l] } -->
   sequent { <H> >- GaProdIsAssoc{'g} Type }

interactive ga_prod_distrib_wf {| intro [intro_typeinf <<'g>>] |} pre_ga[i:l] :
   [wf] sequent { <H> >- 'g in pre_ga[i:l] } -->
   sequent { <H> >- GaProdDistrib{'g} Type }

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
