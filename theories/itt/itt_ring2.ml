doc <:doc<
   @begin[doc]
   @module[Itt_ring]

   This theory defines rings.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 1997-2004 MetaPRL Group

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

doc <:doc< @doc{@parents} >>
extends Itt_group
extends Itt_record_renaming
doc docoff
extends Itt_singleton

open Lm_debug
open Refiner.Refiner.TermOp
open Tactic_type.Tacticals
open Dtactic
open Top_conversionals

open Itt_struct
open Itt_fun
open Itt_record
open Itt_group
open Itt_grouplikeobj
open Itt_squash
open Itt_equal
open Itt_subtype

let _ =
   show_loading "Loading Itt_ring%t"

(************************************************************************
 * RING                                                                 *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @modsection{Ring}
   @modsubsection{Rewrites}

   @end[doc]
>>
define unfold_prering : prering[i:l] <-->
   {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car}

define unfold_isRDistrib : isRDistrib{'r} <-->
   all x: 'r^car. all y: 'r^car. all z: 'r^car. ('x +['r] 'y) *['r] 'z = ('x *['r] 'z) +['r] ('y *['r] 'z) in 'r^car

define unfold_isLDistrib : isLDistrib{'r} <-->
   all x: 'r^car. all y: 'r^car. all z: 'r^car. 'x *['r] ('y +['r] 'z) = ('x *['r] 'y) +['r] ('x *['r] 'z) in 'r^car

define unfold_isDistrib1 : isDistrib{'r} <-->
   isRDistrib{'r} & isLDistrib{'r}

define unfold_isRing1 : isRing{'r} <-->
   isSemigroup{'r} & isGroup{as_additive{'r}} & isCommutative{as_additive{'r}} & isDistrib{'r}

define unfold_ring1 : ring[i:l] <-->
   {R: prering[i:l] | isRing{'R}}
doc docoff

let unfold_isDistrib = unfold_isDistrib1 thenC addrC [1] unfold_isLDistrib thenC addrC [0] unfold_isRDistrib
let unfold_isRing = unfold_isRing1 thenC addrC [0] unfold_isSemigroup thenC addrC [1; 0] unfold_isGroup thenC addrC [1; 1; 0] unfold_isCommutative(* thenC reduceC*) thenC addrC [1; 1; 1] unfold_isDistrib
let unfold_ring = unfold_ring1 thenC addrC [0] unfold_prering thenC addrC [1] unfold_isRing

let fold_isRDistrib = makeFoldC << isRDistrib{'r} >> unfold_isRDistrib
let fold_isLDistrib = makeFoldC << isLDistrib{'r} >> unfold_isLDistrib
let fold_isDistrib = makeFoldC << isDistrib{'r} >> unfold_isDistrib
let fold_prering = makeFoldC << prering[i:l] >> unfold_prering
let fold_isRing1 = makeFoldC << isRing{'R} >> unfold_isRing1
let fold_isRing = makeFoldC << isRing{'R} >> unfold_isRing
let fold_ring1 = makeFoldC << ring[i:l] >> unfold_ring1
let fold_ring = makeFoldC << ring[i:l] >> unfold_ring

let ringDT n = rw unfold_ring n thenT dT n

let resource elim +=
   [<<ring[i:l]>>, ringDT]

(* Rules about distributivity *)
interactive isRDistrib_wf {| intro [] |} :
   sequent { <H> >- 'R^car Type } -->
   sequent { <H>; x: 'R^car; y: 'R^car >- 'x *['R] 'y in 'R^car} -->
   sequent { <H>; x: 'R^car; y: 'R^car >- 'x +['R] 'y in 'R^car} -->
   sequent { <H> >- isRDistrib{'R} Type }

interactive isLDistrib_wf {| intro [] |} :
   sequent { <H> >- 'R^car Type } -->
   sequent { <H>; x: 'R^car; y: 'R^car >- 'x *['R] 'y in 'R^car} -->
   sequent { <H>; x: 'R^car; y: 'R^car >- 'x +['R] 'y in 'R^car} -->
   sequent { <H> >- isLDistrib{'R} Type }

interactive isDistrib_wf {| intro [] |} :
   sequent { <H> >- isRDistrib{'R} Type } -->
   sequent { <H> >- isLDistrib{'R} Type } -->
   sequent { <H> >- isDistrib{'R} Type }

interactive isRDistrib_intro {| intro [] |} :
   sequent { <H> >- 'R^car Type } -->
   sequent { <H>; x: 'R^car; y: 'R^car; z: 'R^car >- ('x +['R] 'y) *['R] 'z = ('x *['R] 'z) +['R] ('y *['R] 'z) in 'R^car } -->
   sequent { <H> >- isRDistrib{'R} }

interactive isLDistrib_intro {| intro [] |} :
   sequent { <H> >- 'R^car Type } -->
   sequent { <H>; x: 'R^car; y: 'R^car; z: 'R^car >- 'x *['R] ('y +['R] 'z) = ('x *['R] 'y) +['R] ('x *['R] 'z) in 'R^car } -->
   sequent { <H> >- isLDistrib{'R} }

interactive isDistrib_intro {| intro [] |} :
   sequent { <H> >- isRDistrib{'R} } -->
   sequent { <H> >- isLDistrib{'R} } -->
   sequent { <H> >- isDistrib{'R} }

interactive isRDistrib_elim {| elim [] |} 'H :
   sequent { <H>; u: isRDistrib{'R}; v: all x: 'R^car. all y: 'R^car. all z: 'R^car. (('x +['R] 'y) *['R] 'z = ('x *['R] 'z) +['R] ('y *['R] 'z) in 'R^car); <J['u]> >- 'C['u] } -->
   sequent { <H>; u: isRDistrib{'R}; <J['u]> >- 'C['u] }

interactive isLDistrib_elim {| elim [] |} 'H :
   sequent { <H>; u: isLDistrib{'R}; v: all x: 'R^car. all y: 'R^car. all z: 'R^car. ('x *['R] ('y +['R] 'z) = ('x *['R] 'y) +['R] ('x *['R] 'z) in 'R^car); <J['u]> >- 'C['u] } -->
   sequent { <H>; u: isLDistrib{'R}; <J['u]> >- 'C['u] }

interactive isDistrib_elim {| elim [] |} 'H :
   sequent { <H>; v: isRDistrib{'R}; w: isLDistrib{'R}; <J['v, 'w]> >- 'C['v, 'w] } -->
   sequent { <H>; u: isDistrib{'R}; <J['u]> >- 'C['u] }

doc <:doc<
   @begin[doc]
   @modsubsection{Well-formedness}

   @end[doc]
>>
interactive prering_wf {| intro [] |} :
   sequent { <H> >- prering[i:l] Type }

interactive isRing_wf {| intro [] |} :
   sequent { <H> >- 'R^car Type } -->
   sequent { <H>; x: 'R^car; y: 'R^car >- 'x *['R] 'y in 'R^car} -->
   sequent { <H>; x: 'R^car; y: 'R^car >- 'x +['R] 'y in 'R^car} -->
   sequent { <H> >- 'R^"0" in 'R^car} -->
   sequent { <H>; x: 'R^car >- 'R^neg 'x in 'R^car} -->
   sequent { <H> >- isRing{'R} Type }

interactive ring_wf {| intro [] |} :
   sequent { <H> >- ring[i:l] Type }
doc docoff

interactive as_additive_car_wf {| intro [] |} :
   [wf] sequent { <H> >- 'R^car Type } -->
   sequent { <H> >- as_additive{'R}^car Type }

doc <:doc<
   @begin[doc]
   @modsubsection{Introduction and Elimination}

   @end[doc]
>>
interactive prering_intro {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'R in {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car} } -->
   sequent { <H> >- 'R in prering[i:l] }

interactive prering_equality {| intro [complete_unless_member] |} :
   sequent { <H> >- 'A = 'B in {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car} } -->
   sequent { <H> >- 'A = 'B in prering[i:l] }

interactive prering_elim {| elim [] |} 'H :
   sequent { <H>; R: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car}; <J['R]> >- 'C['R] } -->
   sequent { <H>; R: prering[i:l]; <J['R]> >- 'C['R] }
doc docoff

interactive car_prering_wf {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} prering[i:l] :
   sequent { <H> >- 'R in prering[i:l] } -->
   sequent { <H> >- 'R^car Type }

interactive addG_isGroup_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'R^car Type } -->
   [main] sequent { <H>; x: 'R^car; y: 'R^car; z: 'R^car >- ('x +['R] 'y) +['R] 'z = 'x +['R] ('y +['R] 'z) in 'R^car } -->
   [main] sequent { <H>; x: 'R^car >- 'R^"0" +['R] 'x = 'x in 'R^car } -->
   [main] sequent { <H>; x: 'R^car >- ('R^neg 'x) +['R] 'x = 'R^"0" in 'R^car } -->
   sequent { <H> >- isGroup{as_additive{'R}} }

interactive addG_isCommut_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'R^car Type } -->
   [main] sequent { <H>; x: 'R^car; y: 'R^car >- 'x +['R] 'y = 'y +['R] 'x in 'R^car} -->
   sequent { <H> >- isCommutative{as_additive{'R}} }

doc <:doc< >>
interactive isRing_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'R^car Type } -->
   [main] sequent { <H> >- isSemigroup{'R} } -->
   [main] sequent { <H> >- isGroup{as_additive{'R}} } -->
   [main] sequent { <H> >- isCommutative{as_additive{'R}} } -->
   [main] sequent { <H> >- isDistrib{'R} } -->
   sequent { <H> >- isRing{'R} }

interactive isRing_elim1 {| elim [] |} 'H :
   sequent { <H>; u: isRing{'R}; u1: isSemigroup{'R}; u2: isGroup{as_additive{'R}}; u3: isCommutative{as_additive{'R}}; u4: isDistrib{'R}; <J['u]> >- 'C['u] } -->
   sequent { <H>; u: isRing{'R}; <J['u]> >- 'C['u] }

interactive isRing_elim {| elim [] |} 'H :
   sequent { <H>; u: isRing{'R}; u1: all x: 'R^car. all y: 'R^car. all z: 'R^car. (('x *['R] 'y) *['R] 'z = 'x *['R] ('y *['R] 'z) in 'R^car); u2: all x: 'R^car. all y: 'R^car. all z: 'R^car. (('x +['R] 'y) +['R] 'z = 'x +['R] ('y +['R] 'z) in 'R^car); v2: all x: 'R^car. ('R^"0" +['R] 'x = 'x in 'R^car); w2: all x: 'R^car. ('R^neg 'x) +['R] 'x = 'R^"0" in 'R^car; u3: all x: 'R^car. all y: 'R^car. ('x +['R] 'y = 'y +['R] 'x in 'R^car); u4: all x: 'R^car. all y: 'R^car. all z: 'R^car. (('x +['R] 'y) *['R] 'z = ('x *['R] 'z) +['R] ('y *['R] 'z) in 'R^car); u5: all x: 'R^car. all y: 'R^car. all z: 'R^car. ('x *['R] ('y +['R] 'z) = ('x *['R] 'y) +['R] ('x *['R] 'z) in 'R^car); <J['u]> >- 'C['u] } -->
   sequent { <H>; u: isRing{'R}; <J['u]> >- 'C['u] }

interactive ring_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'R in prering[i:l] } -->
   [main] sequent { <H> >- isRing{'R} } -->
   sequent { <H> >- 'R in ring[i:l] }

interactive ring_equality {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'A = 'B in prering[i:l] } -->
   [main] sequent { <H> >- isRing{'A} } -->
   sequent { <H> >- 'A = 'B in ring[i:l] }

interactive ring_elim1 {| elim [] |} 'H :
   sequent { <H>; R: prering[i:l]; u: isRing{'R}; <J['R]> >- 'C['R] } -->
   sequent { <H>; R: ring[i:l]; <J['R]> >- 'C['R] }

interactive ring_elim {| elim [] |} 'H :
   sequent { <H>; R: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car}; u1: all x: 'R^car. all y: 'R^car. all z: 'R^car. (('x *['R] 'y) *['R] 'z = 'x *['R] ('y *['R] 'z) in 'R^car); u2: all x: 'R^car. all y: 'R^car. all z: 'R^car. (('x +['R] 'y) +['R] 'z = 'x +['R] ('y +['R] 'z) in 'R^car); v2: all x: 'R^car. ('R^"0" +['R] 'x = 'x in 'R^car); w2: all x: 'R^car. ('R^neg 'x) +['R] 'x = 'R^"0" in 'R^car; u3: all x: 'R^car. all y: 'R^car. ('x +['R] 'y = 'y +['R] 'x in 'R^car); u4: all x: 'R^car. all y: 'R^car. all z: 'R^car. (('x +['R] 'y) *['R] 'z = ('x *['R] 'z) +['R] ('y *['R] 'z) in 'R^car); u5: all x: 'R^car. all y: 'R^car. all z: 'R^car. ('x *['R] ('y +['R] 'z) = ('x *['R] 'y) +['R] ('x *['R] 'z) in 'R^car); <J['R]> >- 'C['R] } -->
   sequent { <H>; R: ring[i:l]; <J['R]> >- 'C['R] }

interactive car_wf {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'R^car Type }

interactive car_wf2 {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'R^car in univ[i:l] }

interactive add_wf {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'R^"+" in 'R^car -> 'R^car -> 'R^car }

interactive neg_wf {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'R^neg in 'R^car -> 'R^car }

interactive mul_wf {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'R^"*" in 'R^car -> 'R^car -> 'R^car }

interactive add_in_car {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'b in 'R^car } -->
   sequent { <H> >- 'a +['R] 'b in 'R^car }

interactive mul_in_car {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'b in 'R^car } -->
   sequent { <H> >- 'a *['R] 'b in 'R^car }

interactive addid_in_car {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'R^"0" in 'R^car }

interactive neg_in_car {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'R^neg 'a in 'R^car }

interactive ring_add_assoc {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'b in 'R^car } -->
   sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- ('a +['R] 'b) +['R] 'c = 'a +['R] ('b +['R] 'c) in 'R^car }

interactive ring_add_assoc2 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'b in 'R^car } -->
   sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- 'a +['R] ('b +['R] 'c) = ('a +['R] 'b) +['R] 'c in 'R^car }

interactive ring_mul_assoc {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'b in 'R^car } -->
   sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- ('a *['R] 'b) *['R] 'c = 'a *['R] ('b *['R] 'c) in 'R^car }

interactive ring_mul_assoc2 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'b in 'R^car } -->
   sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- 'a *['R] ('b *['R] 'c) = ('a *['R] 'b) *['R] 'c in 'R^car }

interactive ring_left_addid {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'R^"0" +['R] 'a = 'a in 'R^car }

interactive ring_left_addid2 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'a = 'R^"0" +['R] 'a in 'R^car }

interactive ring_left_neg {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- ('R^neg 'a) +['R] 'a = 'R^"0" in 'R^car }

interactive ring_left_neg2 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'R^"0" = ('R^neg 'a) +['R] 'a in 'R^car }

interactive add_eq1 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'a = 'b in 'R^car } -->
   sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- 'a +['R] 'c = 'b +['R] 'c in 'R^car }

interactive add_eq2 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'a = 'b in 'R^car } -->
   sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- 'c +['R] 'a = 'c +['R] 'b in 'R^car }

interactive mul_eq1 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'a = 'b in 'R^car } -->
   sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- 'a *['R] 'c = 'b *['R] 'c in 'R^car }

interactive mul_eq2 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'a = 'b in 'R^car } -->
   sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- 'c *['R] 'a = 'c *['R] 'b in 'R^car }

doc docoff

doc <:doc<
   @begin[doc]
   @modsection{Hierarchy}
   A ring is an Abelian group under addition and a semigroup under multiplication.

   @end[doc]
>>
interactive ring_subtype_semigroup {| intro [] |} :
   sequent { <H> >- ring[i:l] subtype semigroup[i:l] }

interactive ring_additive_group {| intro [] |} :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- as_additive{'R} in group[i:l] }

interactive ring_additive_abelgroup {| intro [] |} :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- as_additive{'R} in abelg[i:l] }

doc docoff

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let inf_addid _ _ _ eqs opt_eqs defs t =
   let t, _ = dest_field t in
   let car = mk_field_term t "car" in
      eqs, opt_eqs, defs, car

let inf_neg _ _ _ eqs opt_eqs defs t =
   let t, _ = dest_field t in
   let car = mk_field_term t "car" in
      eqs, opt_eqs, defs, mk_fun_term car car

let inf_add _ _ _ eqs opt_eqs defs t =
   let t, _ = dest_field t in
   let car = mk_field_term t "car" in
      eqs, opt_eqs, defs, mk_fun_term car (mk_fun_term car car)

let resource typeinf += [
   <<'g^"0">>, inf_addid;
   <<'g^"neg">>, inf_neg;
   <<'g^"+">>, inf_add
]

(************************************************************************
 * RING EXAMPLES                                                        *
 ************************************************************************)
doc <:doc<
   @begin[doc]
   @modsection{Ring Examples}
   Zero Ring - The singleton set {0}. It is the simplest possible ring and
   is also called trivial ring.

   @end[doc]
>>
interactive zero_ring :
   sequent { <H> >- {car=singleton{0; int}; "*"=lambda{x. lambda{y. 'x *@ 'y}}; "+"=lambda{x. lambda{y. 'x +@ 'y}}; "0"=0; neg=lambda{x. (-'x)}} in ring[i:l] }

doc docoff

interactive mul_addid1 {| intro [intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'a *['R] 'R^"0" = 'R^"0" in 'R^car }

interactive mul_addid2 {| intro [intro_typeinf <<'R>>] |} ring[i:l] :
   sequent { <H> >- 'R in ring[i:l] } -->
   sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'R^"0" *['R] 'a = 'R^"0" in 'R^car }

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_neg
prec prec_add

prec prec_add < prec_neg

dform ring_df1 : except_mode[src] :: except_mode[prl] :: ring[i:l] =
   mathbbR `"ing" sub{slot[i:l]}

dform ring_df2 : mode[prl] :: ring[i:l] =
   `"Ring[" slot[i:l] `"]"

dform prering_df1 : except_mode[src] :: except_mode[prl] :: prering[i:l] =
   `"prering" sub{slot[i:l]}

dform prering_df2 : mode[prl] :: prering[i:l] =
   `"prering[" slot[i:l] `"]"

dform isRing_df : except_mode[src] :: isRing{'R} =
   `"isRing(" slot{'R} `")"

dform add_df1 : except_mode[src] :: except_mode[prl] :: parens :: "prec"[prec_add] :: ('R^"+" 'a 'b) =
   slot{'a} `"+" sub{'R} slot{'b}

dform add_df2 : mode[prl] :: parens :: "prec"[prec_add] :: ('R^"+" 'a 'b) =
   slot["lt"]{'a} `" " slot{'R} `".+ " slot["le"]{'b}

dform addid_df1 : except_mode[src] :: except_mode[prl] :: ('R^"0") =
   0 sub{'R}

dform id_df2 : mode[prl] :: ('R^"0") =
   slot{'R} `".0"

dform neg_df1 : except_mode[src] :: except_mode[prl] :: parens :: "prec"[prec_neg] :: ('R^neg 'a) =
   `"-" sub{'R} slot{'a}

dform neg_df2 : mode[prl] :: parens :: "prec"[prec_neg] :: ('R^neg 'a) =
   slot{'R} `".neg " slot{'a}

dform isRDistrib_df : except_mode[src] :: isRDistrib{'R} =
   `"isRDistrib(" slot{'R} `")"

dform isLDistrib_df : except_mode[src] :: isLDistrib{'R} =
   `"isLDistrib(" slot{'R} `")"

dform isDistrib_df : except_mode[src] :: isDistrib{'R} =
   `"isDistrib(" slot{'R} `")"

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
