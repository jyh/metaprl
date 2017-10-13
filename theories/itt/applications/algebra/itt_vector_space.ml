doc <:doc<
   @module[Itt_field]

   This theory defines fields.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2004-2017 MetaPRL Group

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

   Author: Xin Yu @email{xiny@cs.caltech.edu}
   @end[license]
>>

doc <:doc< @parents >>
extends Itt_field2
extends Itt_labels
doc docoff

open Basic_tactics

(************************************************************************
 * Vector space
 *)

doc <:doc<
     @modsection{Vector space}

     A vector space is a field $F$ together with a set $V$ and two operations that satisfy
     the axioms of the vector space.

     @modsubsection{Rewrites}
>>
define unfold_pre_vector_space : pre_vector_space[i:l] <-->
   record["0v":t]{r. 'r^vec;
   record["+|":t]{r. 'r^vec -> 'r^vec -> 'r^vec;
   record["*|":t]{r. 'r^car -> 'r^vec -> 'r^vec;
   record["vec":t]{r. univ[i:l];
   prefield[i:l]}}}}

define unfold_vs_add_is_commutative : VsAddIsCommutative{'g} <-->
   all x: 'g^vec. all y: 'g^vec. ('x +|['g] 'y = 'y +|['g] 'x in 'g^vec)

define unfold_vs_add_is_assoc : VsAddIsAssoc{'g} <-->
   all x: 'g^vec. all y: 'g^vec. all z: 'g^vec. (('x +|['g] ('y +|['g] 'z)) = (('x +|['g] 'y) +|['g] 'z) in 'g^vec)

define unfold_vs_zero_is_identity : VsZeroIsIdentity{'g} <-->
   all x: 'g^vec. (('x +|['g] 'g^"0v") = 'x in 'g^vec)

define unfold_vs_add_has_inverse : VsAddHasInverse{'g} <-->
   all x: 'g^vec. exst y: 'g^vec. (('x +|['g] 'y) = 'g^"0v" in 'g^vec)

define unfold_vs_mul_is_compat : VsMulIsCompat{'g} <-->
   all a: 'g^car. all b: 'g^car. all x: 'g^vec. (('a *|['g] ('b *|['g] 'x)) = (('a *['g] 'b) *|['g] 'x) in 'g^vec)

define unfold_vs_mul_has_identity : VsMulHasIdentity{'g} <-->
   all x: 'g^vec. (('g^"1" *|['g] 'x) = 'x in 'g^vec)

define unfold_vs_mul_vec_distrib : VsMulVecDistrib{'g} <-->
   all a: 'g^car. all x: 'g^vec. all y: 'g^vec. (('a *|['g] ('x +|['g] 'y)) = (('a *|['g] 'x) +|['g] ('a *|['g] 'y)) in 'g^vec)

define unfold_vs_mul_scalar_distrib : VsMulScalarDistrib{'g} <-->
   all a: 'g^car. all b: 'g^car. all x: 'g^vec. ((('a +['g] 'b) *|['g] 'x) = (('a *|['g] 'x) +|['g] ('b *|['g] 'x)) in 'g^vec)

define unfold_is_vector_space : isVectorSpace{'g} <-->
   isField{'g} &
   VsAddIsCommutative{'g} &
   VsAddIsAssoc{'g} &
   VsZeroIsIdentity{'g} &
   VsAddHasInverse{'g} &
   VsMulIsCompat{'g} &
   VsMulHasIdentity{'g} &
   VsMulVecDistrib{'g} &
   VsMulScalarDistrib{'g}

define unfold_vector_space : vector_space[i:l] <-->
   {f: pre_vector_space[i:l] | isVectorSpace{'f}}

doc docoff

let fold_pre_vector_space = makeFoldC << pre_vector_space[i:l] >> unfold_pre_vector_space
let fold_is_vector_space = makeFoldC << isVectorSpace{'f} >> unfold_is_vector_space

doc <:doc<
   @modsubsection{Well-formedness}

>>
interactive pre_vector_space_wf {| intro [] |} :
   sequent { <H> >- pre_vector_space[i:l] Type }

interactive pre_vector_space_elim {| elim [] |} 'H  :
   sequent { <H>;
      g: record["0v":t]{r. 'r^vec;
         record["+|":t]{r. 'r^vec -> 'r^vec -> 'r^vec;
         record["*|":t]{r. 'r^car -> 'r^vec -> 'r^vec;
         record["vec":t]{r. univ[i:l];
         prefield[i:l]}}}};
      <J['g]> >- 'C['g] } -->
   sequent { <H>; g: pre_vector_space[i:l]; <J['g]> >- 'C['g] }

interactive vector_space_car_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   sequent { <H> >- 'g^car Type }

interactive vector_space_vec_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   sequent { <H> >- 'g^vec Type }

interactive vector_space_0v_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   sequent { <H> >- 'g^"0v" IN 'g^vec }

interactive vector_space_scalar_zero_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   sequent { <H> >- 'g^"0" IN 'g^car }

interactive vector_space_scalar_one_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   sequent { <H> >- 'g^"1" IN 'g^car }

interactive vector_space_scalar_neg_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   sequent { <H> >- 'g^neg IN 'g^car -> 'g^car }

interactive vector_space_scalar_inv_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   sequent { <H> >- 'g^inv IN {x: 'g^car| 'x <> 'g^"0" in 'g^car} -> {x: 'g^car| 'x <> 'g^"0" in 'g^car} }

interactive vector_space_scalar_add_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   [wf] sequent { <H> >- 'x IN 'g^car } -->
   [wf] sequent { <H> >- 'y IN 'g^car } -->
   sequent { <H> >- 'x +['g] 'y IN 'g^car }

interactive vector_space_scalar_mul_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   [wf] sequent { <H> >- 'x IN 'g^car } -->
   [wf] sequent { <H> >- 'y IN 'g^car } -->
   sequent { <H> >- 'x *['g] 'y IN 'g^car }

interactive vector_space_add_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   [wf] sequent { <H> >- 'x IN 'g^vec } -->
   [wf] sequent { <H> >- 'y IN 'g^vec } -->
   sequent { <H> >- 'x +|['g] 'y IN 'g^vec }

interactive vector_space_mul_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   [wf] sequent { <H> >- 'a IN 'g^car } -->
   [wf] sequent { <H> >- 'x IN 'g^vec } -->
   sequent { <H> >- 'a *|['g] 'x IN 'g^vec }

interactive vs_add_is_commutative_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   sequent { <H> >- VsAddIsCommutative{'g} Type }

interactive vs_add_is_assoc_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   sequent { <H> >- VsAddIsAssoc{'g} Type }

interactive vs_zero_is_identity_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   sequent { <H> >- VsZeroIsIdentity{'g} Type }

interactive vs_add_has_inverse_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   sequent { <H> >- VsAddHasInverse{'g} Type }

interactive vs_mul_is_compat_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   sequent { <H> >- VsMulIsCompat{'g} Type }

interactive vs_mul_has_identity_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   sequent { <H> >- VsMulHasIdentity{'g} Type }

interactive vs_mul_vec_distrib_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   sequent { <H> >- VsMulVecDistrib{'g} Type }

interactive vs_mul_scalar_distrib_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   sequent { <H> >- VsMulScalarDistrib{'g} Type }

interactive is_vector_space_wf {| intro [intro_typeinf <<'g>>] |} pre_vector_space[i:l] :
   [wf] sequent { <H> >- 'g IN pre_vector_space[i:l] } -->
   sequent { <H> >- isVectorSpace{'g} Type }

interactive vector_space_wf {| intro [] |} :
   sequent { <H> >- vector_space[i:l] Type }

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
