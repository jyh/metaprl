doc <:doc<
   @begin[doc]
   @module[Itt_ring_uce]

   This theory defines commutative unitrings with decidable equality.
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
extends Itt_unitring
extends Itt_ring_e
doc docoff
extends Itt_poly

open Lm_debug
open Tactic_type.Tacticals
open Dtactic
open Top_conversionals

open Itt_grouplikeobj
open Itt_unitring
open Itt_ring_e
open Itt_poly
open Itt_equal

let _ =
   show_loading "Loading Itt_ring_uce%t"

(************************************************************************
 * Commutative unitring with Decidable Equality                             *
 ************************************************************************)
doc <:doc<
   @begin[doc]
   @modsection{Commutative unitring with decidable equality}
   @modsubsection{Rewrites}

   @end[doc]
>>
define unfold_preunitringE1 : preunitringE[i:l] <-->
   record["eq":t]{r. ('r^car -> 'r^car -> bool); preunitring[i:l]}

define unfold_isUnitRingCE1 : isUnitRingCE{'f} <-->
   isUnitRing{'f} & isCommutative{'f} & eqDecidable{'f}

define unfold_unitringCE1 : unitringCE[i:l] <-->
   {f: preunitringE[i:l] | isUnitRingCE{'f}}
doc docoff

let unfold_preunitringE = unfold_preunitringE1 thenC addrC [1] unfold_preunitring
let unfold_isUnitRingCE = unfold_isUnitRingCE1 thenC addrC [0] unfold_isUnitRing thenC addrC [1; 0] unfold_isCommutative thenC addrC [1; 1] unfold_eqDecidable
let unfold_unitringCE = unfold_unitringCE1 thenC addrC [0] unfold_preunitringE thenC addrC [1] unfold_isUnitRingCE

let fold_preunitringE1 = makeFoldC << preunitringE[i:l] >> unfold_preunitringE1
let fold_preunitringE = makeFoldC << preunitringE[i:l] >> unfold_preunitringE
let fold_isUnitRingCE1 = makeFoldC << isUnitRingCE{'f} >> unfold_isUnitRingCE1
let fold_isUnitRingCE = makeFoldC << isUnitRingCE{'f} >> unfold_isUnitRingCE
let fold_unitringCE1 = makeFoldC << unitringCE[i:l] >> unfold_unitringCE1
let fold_unitringCE = makeFoldC << unitringCE[i:l] >> unfold_unitringCE

let unitringCEDT n = rw unfold_unitringCE n thenT dT n

let resource elim +=
   [<<unitringCE[i:l]>>, unitringCEDT]

doc <:doc<
   @begin[doc]
   @modsubsection{Well-formedness}

   @end[doc]
>>
interactive preunitringE_wf {| intro [] |} :
   sequent { <H> >- preunitringE[i:l] Type }

interactive isUnitRingCE_wf {| intro [] |} :
   [wf] sequent { <H> >- isUnitRing{'f} Type } -->
   [wf] sequent { <H> >- isCommutative{'f} Type } -->
   [wf] sequent { <H> >- eqDecidable{'f} Type } -->
   sequent { <H> >- isUnitRingCE{'f} Type }

interactive unitringCE_wf {| intro [] |} :
   sequent { <H> >- unitringCE[i:l] Type }

doc <:doc<
   @begin[doc]
   @modsubsection{Introduction and Elimination}

   @end[doc]
>>
interactive preunitringE_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car; "1": ^car; "eq": ^car -> ^car -> bool} } -->
   sequent { <H> >- 'f in preunitringE[i:l] }

interactive preunitringE_equality {| intro [complete_unless_member] |} :
   [wf] sequent { <H> >- 'A = 'B in {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car; "1": ^car; "eq": ^car -> ^car -> bool} } -->
   sequent { <H> >- 'A = 'B in preunitringE[i:l] }

interactive preunitringE_elim {| elim [] |} 'H :
   sequent { <H>; f: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car; "1": ^car; "eq": ^car -> ^car -> bool}; <J['f]> >- 'C['f] } -->
   sequent { <H>; f: preunitringE[i:l]; <J['f]> >- 'C['f] }
doc docoff

interactive car_preunitringE_wf {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} preunitringE[i:l] :
   [wf] sequent { <H> >- 'f in preunitringE[i:l] } -->
   sequent { <H> >- 'f^car Type }

doc <:doc< @doc{ } >>
interactive isUnitRingCE_intro {| intro [AutoMustComplete] |} :
   sequent { <H> >- isUnitRing{'f} } -->
   sequent { <H> >- isCommutative{'f} } -->
   sequent { <H> >- eqDecidable{'f} } -->
   sequent { <H> >- isUnitRingCE{'f} }

interactive isUnitRingCE_elim1 {| elim [] |} 'H :
   sequent { <H>; u: isUnitRingCE{'f}; x: isUnitRing{'f}; y: isCommutative{'f}; z: eqDecidable{'f}; <J['u]> >- 'C['u] } -->
   sequent { <H>; u: isUnitRingCE{'f}; <J['u]> >- 'C['u] }

interactive isUnitRingCE_elim {| elim [] |} 'H :
   sequent { <H>; u: isUnitRingCE{'f};
      u1: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x *['f] 'y) *['f] 'z = 'x *['f] ('y *['f] 'z) in 'f^car);
      u2: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x +['f] 'y) +['f] 'z = 'x +['f] ('y +['f] 'z) in 'f^car);
      v2: all x: 'f^car. ('f^"0" +['f] 'x = 'x in 'f^car);
      w2: all x: 'f^car. ('f^neg 'x) +['f] 'x = 'f^"0" in 'f^car;
      u3: all x: 'f^car. all y: 'f^car. ('x +['f] 'y = 'y +['f] 'x in 'f^car);
      u4: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x +['f] 'y) *['f] 'z = ('x *['f] 'z) +['f] ('y *['f] 'z) in 'f^car);
      u5: all x: 'f^car. all y: 'f^car. all z: 'f^car. ('x *['f] ('y +['f] 'z) = ('x *['f] 'y) +['f] ('x *['f] 'z) in 'f^car);
      u6: all x: 'f^car. (('f^"1" *['f] 'x = 'x in 'f^car) & ('x *['f] 'f^"1" = 'x in 'f^car));
      u7: all x: 'f^car. all y: 'f^car. ('x *['f] 'y = 'y *['f] 'x in 'f^car);
      u8: all x: 'f^car. all y: 'f^car. "iff"{'x = 'y in 'f^car; "assert"{'f^eq 'x 'y}};
      <J['u]> >- 'C['u] } -->
   sequent { <H>; u: isUnitRingCE{'f}; <J['u]> >- 'C['u] }

interactive unitringCE_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in preunitringE[i:l] } -->
   [main] sequent { <H> >- isUnitRingCE{'f} } -->
   sequent { <H> >- 'f in unitringCE[i:l] }

interactive unitringCE_equality {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'A = 'B in preunitringE[i:l] } -->
   [main] sequent { <H> >- isUnitRingCE{'A} } -->
   sequent { <H> >- 'A = 'B in unitringCE[i:l] }

interactive unitringCE_elim1 {| elim [] |} 'H :
   sequent { <H>; f: preunitringE[i:l]; u: isUnitRingCE{'f}; <J['f]> >- 'C['f] } -->
   sequent { <H>; f: unitringCE[i:l]; <J['f]> >- 'C['f] }

interactive unitringCE_elim {| elim [] |} 'H :
   sequent { <H>;
       f: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car; "1": ^car; "eq": ^car -> ^car -> bool};
      u1: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x *['f] 'y) *['f] 'z = 'x *['f] ('y *['f] 'z) in 'f^car);
      u2: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x +['f] 'y) +['f] 'z = 'x +['f] ('y +['f] 'z) in 'f^car);
      v2: all x: 'f^car. ('f^"0" +['f] 'x = 'x in 'f^car);
      w2: all x: 'f^car. ('f^neg 'x) +['f] 'x = 'f^"0" in 'f^car;
      u3: all x: 'f^car. all y: 'f^car. ('x +['f] 'y = 'y +['f] 'x in 'f^car);
      u4: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x +['f] 'y) *['f] 'z = ('x *['f] 'z) +['f] ('y *['f] 'z) in 'f^car);
      u5: all x: 'f^car. all y: 'f^car. all z: 'f^car. ('x *['f] ('y +['f] 'z) = ('x *['f] 'y) +['f] ('x *['f] 'z) in 'f^car);
      u6: all x: 'f^car. (('f^"1" *['f] 'x = 'x in 'f^car) & ('x *['f] 'f^"1" = 'x in 'f^car));
      u7: all x: 'f^car. all y: 'f^car. ('x *['f] 'y = 'y *['f] 'x in 'f^car);
      u8: all x: 'f^car. all y: 'f^car. "iff"{'x = 'y in 'f^car; "assert"{'f^eq 'x 'y}};
      <J['f]> >- 'C['f] } -->
   sequent { <H>; f: unitringCE[i:l]; <J['f]> >- 'C['f] }

doc <:doc<
   @begin[doc]
   @modsubsection{Properties}

   @end[doc]
>>
interactive car_wf {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   sequent { <H> >- 'R^car Type }

interactive car_wf2 {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   sequent { <H> >- 'R^car in univ[i:l] }

interactive add_wf {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   sequent { <H> >- 'R^"+" in 'R^car -> 'R^car -> 'R^car }

interactive neg_wf {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   sequent { <H> >- 'R^neg in 'R^car -> 'R^car }

interactive mul_wf {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   sequent { <H> >- 'R^"*" in 'R^car -> 'R^car -> 'R^car }

interactive eq_wf {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   sequent { <H> >- 'R^"eq" in 'R^car -> 'R^car -> bool }

interactive add_in_car {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'b in 'R^car } -->
   sequent { <H> >- 'a +['R] 'b in 'R^car }

interactive mul_in_car {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'b in 'R^car } -->
   sequent { <H> >- 'a *['R] 'b in 'R^car }

interactive eq_in_bool {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'b in 'R^car } -->
   sequent { <H> >- 'R^eq 'a 'b in bool }

interactive addid_in_car {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   sequent { <H> >- 'R^"0" in 'R^car }

interactive id_in_car {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   sequent { <H> >- 'R^"1" in 'R^car }

interactive neg_in_car {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'R^neg 'a in 'R^car }

interactive ringuce_add_assoc {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'b in 'R^car } -->
   [wf] sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- ('a +['R] 'b) +['R] 'c = 'a +['R] ('b +['R] 'c) in 'R^car }

interactive ringuce_add_assoc2 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'b in 'R^car } -->
   [wf] sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- 'a +['R] ('b +['R] 'c) = ('a +['R] 'b) +['R] 'c in 'R^car }

interactive ringuce_mul_assoc {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'b in 'R^car } -->
   [wf] sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- ('a *['R] 'b) *['R] 'c = 'a *['R] ('b *['R] 'c) in 'R^car }

interactive ringuce_mul_assoc2 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'b in 'R^car } -->
   [wf] sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- 'a *['R] ('b *['R] 'c) = ('a *['R] 'b) *['R] 'c in 'R^car }

interactive ringuce_add_commut {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'b in 'R^car } -->
   sequent { <H> >- 'a +['R] 'b = 'b +['R] 'a in 'R^car }

interactive ringuce_mul_commut {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'b in 'R^car } -->
   sequent { <H> >- 'a *['R] 'b = 'b *['R] 'a in 'R^car }

interactive ringuce_left_addid {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'R^"0" +['R] 'a = 'a in 'R^car }

interactive ringuce_left_addid2 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'a = 'R^"0" +['R] 'a in 'R^car }

interactive ringuce_right_addid {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'a +['R] 'R^"0" = 'a in 'R^car }

interactive ringuce_right_addid2 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'a = 'a +['R] 'R^"0" in 'R^car }

interactive ringuce_left_id {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'R^"1" *['R] 'a = 'a in 'R^car }

interactive ringuce_left_id2 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'a = 'R^"1" *['R] 'a in 'R^car }

interactive ringuce_right_id {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'a *['R] 'R^"1" = 'a in 'R^car }

interactive ringuce_right_id2 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'a = 'a *['R] 'R^"1" in 'R^car }

interactive ringuce_left_neg {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- ('R^neg 'a) +['R] 'a = 'R^"0" in 'R^car }

interactive ringuce_left_neg2 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'R^"0" = ('R^neg 'a) +['R] 'a in 'R^car }

interactive ringuce_right_neg {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'a +['R] ('R^neg 'a) = 'R^"0" in 'R^car }

interactive ringuce_right_neg2 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'R^"0" = 'a +['R] ('R^neg 'a) in 'R^car }

interactive ringuce_right_distib {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'b in 'R^car } -->
   [wf] sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- ('a +['R] 'b) *['R] 'c = ('a *['R] 'c) +['R] ('b *['R] 'c) in 'R^car }

interactive ringuce_right_distib1 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'b in 'R^car } -->
   [wf] sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- ('a *['R] 'c) +['R] ('b *['R] 'c) = ('a +['R] 'b) *['R] 'c in 'R^car }

interactive ringuce_left_distib {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'b in 'R^car } -->
   [wf] sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- 'a *['R] ('b +['R] 'c) = ('a *['R] 'b) +['R] ('a *['R] 'c) in 'R^car }

interactive ringuce_eqDecidable {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'b in 'R^car } -->
   [wf] sequent { <H> >- 'a = 'b in 'R^car } -->
   sequent { <H> >- "assert"{'R^eq 'a 'b} }

interactive ringuce_eqDecidable1 unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'b in 'R^car } -->
   [wf] sequent { <H> >- "assert"{'R^eq 'a 'b} } -->
   sequent { <H> >- 'a = 'b in 'R^car }

interactive ringuce_isZero {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'a = 'R^"0" in 'R^car } -->
   sequent { <H> >- "assert"{isZero{'a; 'R}} }

interactive ringuce_isZero2 unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- "assert"{isZero{'a; 'R}} } -->
   sequent { <H> >- 'a = 'R^"0" in 'R^car }

interactive ringuce_left_distib1 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'b in 'R^car } -->
   [wf] sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- ('a *['R] 'b) +['R] ('a *['R] 'c) = 'a *['R] ('b +['R] 'c) in 'R^car }

interactive add_eq1 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a = 'b in 'R^car } -->
   [wf] sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- 'a +['R] 'c = 'b +['R] 'c in 'R^car }

interactive add_eq2 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a = 'b in 'R^car } -->
   [wf] sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- 'c +['R] 'a = 'c +['R] 'b in 'R^car }

interactive mul_eq1 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a = 'b in 'R^car } -->
   [wf] sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- 'a *['R] 'c = 'b *['R] 'c in 'R^car }

interactive mul_eq2 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a = 'b in 'R^car } -->
   [wf] sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- 'c *['R] 'a = 'c *['R] 'b in 'R^car }

doc <:doc<
   @begin[doc]
   @modsection{Hierarchy}

   @end[doc]
>>
interactive unitringCE_subtype_unitring {| intro [] |} :
   sequent { <H> >- unitringCE[i:l] subtype unitring[i:l] }

interactive unitringCE_subtype_ring {| intro [] |} :
   sequent { <H> >- unitringCE[i:l] subtype ring[i:l] }
doc docoff

(************************************************************************
 * Polynomials                                                          *
 ************************************************************************)
doc <:doc<
   @begin[doc]
   @modsection{Polynomial ring}
   @modsubsection{Rewrites}

   @end[doc]
>>
define unfold_poly_ring : poly_ring{'F} <-->
   { car = poly{'F};
     "*" = lambda{p. lambda{q. mul_poly{'p; 'q; 'F}}};
     "+" = lambda{p. lambda{q. add_poly{'p; 'q; 'F}}};
     "0" = zero_poly{'F};
     neg = lambda{p. neg_poly{'p; 'F}};
     "1" = unit_poly{'F};
     "eq" = lambda{p. lambda{q. eq_poly{'p; 'q; 'F}}}
   }
doc docoff

let fold_poly_ring = makeFoldC << poly_ring{'F} >> unfold_poly_ring

interactive neg_neg1 {| intro [intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'a = 'R^neg ('R^neg 'a) in 'R^car }

interactive neg_neg2 {| intro [intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'R^neg ('R^neg 'a) = 'a in 'R^car }

interactive neg_of_addid {| intro [intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   sequent { <H> >- 'R^neg 'R^"0" = 'R^"0" in 'R^car }

interactive neg_of_addid2 {| intro [intro_typeinf <<'R>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
   sequent { <H> >- 'R^"0" = 'R^neg 'R^"0" in 'R^car }


interactive ringpoly_coeff_addpoly {| intro [AutoMustComplete; intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   [wf] sequent { <H> >- 'n in nat } -->
   sequent { <H> >- coeff{add_poly{'p; 'q; 'F}; 'n; 'F} = coeff{'p; 'n; 'F} +@ coeff{'q; 'n; 'F} in 'F^car }


interactive ringpoly_add_assoc {| intro [AutoMustComplete; intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   [wf] sequent { <H> >- 't in poly{'F} } -->
   sequent { <H> >- add_poly{add_poly{'p; 'q; 'F}; 't; 'F} = add_poly{'p; add_poly{'q; 't; 'F}; 'F} in poly{'F} }

interactive ringpoly_add_assoc2 {| intro [AutoMustComplete; intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   [wf] sequent { <H> >- 't in poly{'F} } -->
   sequent { <H> >- add_poly{'p; add_poly{'q; 't; 'F}; 'F} = add_poly{add_poly{'p; 'q; 'F}; 't; 'F} in poly{'F} }

interactive ringpoly_mul_assoc {| intro [AutoMustComplete; intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   [wf] sequent { <H> >- 't in poly{'F} } -->
   sequent { <H> >- mul_poly{mul_poly{'p; 'q; 'F}; 't; 'F} = mul_poly{'p; mul_poly{'q; 't; 'F}; 'F} in poly{'F} }

interactive ringpoly_mul_assoc2 {| intro [AutoMustComplete; intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   [wf] sequent { <H> >- 't in poly{'F} } -->
   sequent { <H> >- mul_poly{'p; mul_poly{'q; 't; 'F}; 'F} = mul_poly{mul_poly{'p; 'q; 'F}; 't; 'F} in poly{'F} }

interactive ringpoly_addid {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   sequent { <H> >- add_poly{zero_poly{'F}; 'p; 'F} = 'p in poly{'F} }

interactive ringpoly_addid2 {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   sequent { <H> >- 'p = add_poly{zero_poly{'F}; 'p; 'F} in poly{'F} }

interactive ringpoly_left_neg {| intro [AutoMustComplete; intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   sequent { <H> >- add_poly{neg_poly{'p; 'F}; 'p; 'F} = zero_poly{'F} in poly{'F} }

interactive ringpoly_left_neg2 {| intro [AutoMustComplete; intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   sequent { <H> >- zero_poly{'F} = add_poly{neg_poly{'p; 'F}; 'p; 'F} in poly{'F} }

interactive ringpoly_left_id {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   sequent { <H> >- mul_poly{unit_poly{'F}; 'p; 'F} = 'p in poly{'F} }

interactive ringpoly_left_id2 {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   sequent { <H> >- 'p = mul_poly{unit_poly{'F}; 'p; 'F} in poly{'F} }

interactive ringpoly_add_commut {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   sequent { <H> >- add_poly{'p; 'q; 'F} = add_poly{'q; 'p; 'F} in poly{'F} }

interactive ringpoly_mul_commut {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   sequent { <H> >- mul_poly{'p; 'q; 'F} = mul_poly{'q; 'p; 'F} in poly{'F} }

interactive ringpoly_right_id {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   sequent { <H> >- mul_poly{'p; unit_poly{'F}; 'F} = 'p in poly{'F} }

interactive ringpoly_right_id2 {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   sequent { <H> >- 'p = mul_poly{'p; unit_poly{'F}; 'F} in poly{'F} }

interactive ringpoly_right_distrib {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   [wf] sequent { <H> >- 't in poly{'F} } -->
   sequent { <H> >- mul_poly{add_poly{'p; 'q; 'F}; 't; 'F} = add_poly{mul_poly{'p; 't; 'F}; mul_poly{'q; 't; 'F}; 'F} in poly{'F} }

interactive ringpoly_right_distrib1 {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   [wf] sequent { <H> >- 't in poly{'F} } -->
   sequent { <H> >- add_poly{mul_poly{'p; 't; 'F}; mul_poly{'q; 't; 'F}; 'F} = mul_poly{add_poly{'p; 'q; 'F}; 't; 'F} in poly{'F} }

interactive ringpoly_left_distrib {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   [wf] sequent { <H> >- 't in poly{'F} } -->
   sequent { <H> >- mul_poly{'p; add_poly{'q; 't; 'F}; 'F} = add_poly{mul_poly{'p; 'q; 'F}; mul_poly{'p; 't; 'F}; 'F} in poly{'F} }

interactive ringpoly_left_distrib1 {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   [wf] sequent { <H> >- 't in poly{'F} } -->
   sequent { <H> >- add_poly{mul_poly{'p; 'q; 'F}; mul_poly{'p; 't; 'F}; 'F} = mul_poly{'p; add_poly{'q; 't; 'F}; 'F} in poly{'F} }

(*interactive eval_add_distrib {| intro [intro_typeinf <<'F>>] |} fieldE[i:l] :
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   [wf] sequent { <H> >- 'a in 'F^car } -->
   [wf] sequent { <H> >- 'F in fieldE[i:l] } -->
   sequent { <H> >- eval_poly{'p; 'a; 'F} +['F] eval_poly{'q; 'a; 'F} = eval_poly{add_poly{'p; 'q; 'F}; 'a; 'F} in 'F^car }

interactive eval_mul_distrib {| intro [intro_typeinf <<'F>>] |} fieldE[i:l] :
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   [wf] sequent { <H> >- 'a in 'F^car } -->
   [wf] sequent { <H> >- 'F in fieldE[i:l] } -->
   sequent { <H> >- eval_poly{'p; 'a; 'F} *['F] eval_poly{'q; 'a; 'F} = eval_poly{mul_poly{'p; 'q; 'F}; 'a; 'F} in 'F^car }
*)
interactive ringpoly_eqdec {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   [wf] sequent { <H> >- 'p = 'q in poly{'F} } -->
   sequent { <H> >- "assert"{eq_poly{'p; 'q; 'F}} }

interactive ringpoly_eqdec2 unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   [wf] sequent { <H> >- "assert"{eq_poly{'p; 'q; 'F}} } -->
   sequent { <H> >- 'p = 'q in poly{'F} }

doc <:doc<
   @begin[doc]
   @modsubsection{Properties}

   @end[doc]
>>
interactive poly_ring_uce {| intro [] |} :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   sequent { <H> >- poly_ring{'F} in unitringCE[i:l] }
doc docoff

(************************************************************************
 * DISPLAY FOfMS                                                        *
 ************************************************************************)

dform unitringCE_df1 : except_mode[src] :: except_mode[prl] :: unitringCE[i:l] =
   mathbbU `"nitringCE" sub{slot[i:l]}

dform unitringCE_df2 : mode[prl] :: unitringCE[i:l] =
   `"UnitringCE[" slot[i:l] `"]"

dform preunitringE_df1 : except_mode[src] :: except_mode[prl] :: preunitringE[i:l] =
   `"preunitringE" sub{slot[i:l]}

dform preunitringE_df2 : mode[prl] :: preunitringE[i:l] =
   `"preunitringE[" slot[i:l] `"]"

dform isUnitRingCE_df : except_mode[src] :: isUnitRingCE{'F} =
   `"isUnitRingCE(" slot{'F} `")"

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
