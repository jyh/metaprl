doc <:doc<
   @begin[doc]
   @module[Itt_field]

   This theory defines fields.
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
extends Itt_ring2
extends Itt_record_renaming
doc docoff
extends Itt_unitring
extends Itt_intdomain

open Lm_debug
open Lm_printf

open Basic_tactics

open Itt_grouplikeobj
open Itt_ring2
open Itt_equal
open Itt_record_label

let _ =
   show_loading "Loading Itt_field%t"

(************************************************************************
 * FIELD                                                                *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @modsection{Field}
   @modsubsection{Rewrites}

   @end[doc]
>>
define unfold_prefield1 : prefield[i:l] <-->
   record["inv":t]{r. ({x: 'r^car| 'x <> 'r^"0" in 'r^car} -> {x: 'r^car| 'x <> 'r^"0" in 'r^car}); record["1":t]{r. 'r^car; prering[i:l]}}

define unfold_isField1 : isField{'f} <-->
   isRing{'f} & isCommutative{'f} & all x: 'f^car. 'f^"1" *['f] 'x = 'x in 'f^car & all x: {x: 'f^car | 'x <> 'f^"0" in 'f^car}. ('f^inv 'x) *['f] 'x = 'f^"1" in 'f^car & ('f^"0" <> 'f^"1" in 'f^car)

define unfold_field1 : field[i:l] <-->
   {f: prefield[i:l] | isField{'f}}
doc docoff

let unfold_prefield = unfold_prefield1 thenC addrC [Subterm 2; Subterm 2] unfold_prering
let unfold_isField = unfold_isField1 thenC addrC [Subterm 1] unfold_isRing thenC addrC [Subterm 2; Subterm 1] unfold_isCommutative
let unfold_field = unfold_field1 thenC addrC [Subterm 1] unfold_prefield thenC addrC [Subterm 2] unfold_isField

let fold_prefield1 = makeFoldC << prefield[i:l] >> unfold_prefield1
let fold_prefield = makeFoldC << prefield[i:l] >> unfold_prefield
let fold_isField1 = makeFoldC << isField{'f} >> unfold_isField1
let fold_isField = makeFoldC << isField{'f} >> unfold_isField
let fold_field1 = makeFoldC << field[i:l] >> unfold_field1
let fold_field = makeFoldC << field[i:l] >> unfold_field

let fieldDT n = rw unfold_field n thenT dT n

let resource elim +=
   [<<field[i:l]>>, fieldDT]

doc <:doc<
   @begin[doc]
   @modsubsection{Well-formedness}

   @end[doc]
>>
interactive prefield_wf {| intro [] |} :
   sequent { <H> >- prefield[i:l] Type }

interactive isField_wf {| intro [] |} :
   sequent { <H>; x: 'f^car; y: 'f^car >- 'x *['f] 'y in 'f^car} -->
   sequent { <H>; x: 'f^car; y: 'f^car >- 'x +['f] 'y in 'f^car} -->
   [wf] sequent { <H> >- 'f^"0" in 'f^car} -->
   [wf] sequent { <H> >- 'f^"1" in 'f^car} -->
   sequent { <H>; x: 'f^car >- 'f^neg 'x in 'f^car} -->
   sequent { <H>; x: 'f^car; y: 'x <> 'f^"0" in 'f^car >- 'f^inv 'x in 'f^car} -->
   sequent { <H> >- isField{'f} Type }

interactive field_wf {| intro [] |} :
   sequent { <H> >- field[i:l] Type }

doc <:doc<
   @begin[doc]
   @modsubsection{Introduction and Elimination}

   @end[doc]
>>
interactive prefield_intro {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'f in {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car; "1": ^car; inv: {x: ^car| 'x <> ^"0" in ^car} -> {x: ^car| 'x <> ^"0" in ^car}} } -->
   sequent { <H> >- 'f in prefield[i:l] }

interactive prefield_equality {| intro [complete_unless_member] |} :
   sequent { <H> >- 'A = 'B in {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car; "1": ^car; inv: {x: ^car| 'x <> ^"0" in ^car} -> {x: ^car| 'x <> ^"0" in ^car}} } -->
   sequent { <H> >- 'A = 'B in prefield[i:l] }

interactive prefield_elim {| elim [] |} 'H :
   sequent { <H>; f: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car; "1": ^car; inv: {x: ^car| 'x <> ^"0" in ^car} -> {x: ^car| 'x <> ^"0" in ^car}}; <J['f]> >- 'C['f] } -->
   sequent { <H>; f: prefield[i:l]; <J['f]> >- 'C['f] }
doc docoff

interactive car_prefield_wf {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} prefield[i:l] :
   [wf] sequent { <H> >- 'f in prefield[i:l] } -->
   sequent { <H> >- 'f^car Type }

doc docon
interactive isField_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f^"0" in 'f^car } -->
   [main] sequent { <H> >- isRing{'f} } -->
   [main] sequent { <H> >- isCommutative{'f} } -->
   [main] sequent { <H>; x: 'f^car >- 'f^"1" *['f] 'x = 'x in 'f^car } -->
   [main] sequent { <H>; x: 'f^car; y: 'x <> 'f^"0" in 'f^car >- ('f^inv 'x) *['f] 'x = 'f^"1" in 'f^car } -->
   [main] sequent { <H> >- 'f^"0" <> 'f^"1" in 'f^car } -->
   sequent { <H> >- isField{'f} }

interactive isField_elim1 {| elim [] |} 'H :
   sequent { <H>; u: isField{'f}; u1: isRing{'f}; u2: isCommutative{'f}; u3: all x: 'f^car. ('f^"1" *['f] 'x = 'x in 'f^car); u4: all x: {x: 'f^car | 'x <> 'f^"0" in 'f^car}. (('f^inv 'x) *['f] 'x = 'f^"1" in 'f^car); u5: 'f^"0" <> 'f^"1" in 'f^car; <J['u]> >- 'C['u] } -->
   sequent { <H>; u: isField{'f}; <J['u]> >- 'C['u] }

interactive isField_elim {| elim [] |} 'H :
   sequent { <H>; u: isField{'f};
      u1: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x *['f] 'y) *['f] 'z = 'x *['f] ('y *['f] 'z) in 'f^car);
      u2: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x +['f] 'y) +['f] 'z = 'x +['f] ('y +['f] 'z) in 'f^car);
      v2: all x: 'f^car. ('f^"0" +['f] 'x = 'x in 'f^car);
      w2: all x: 'f^car. ('f^neg 'x) +['f] 'x = 'f^"0" in 'f^car;
      u3: all x: 'f^car. all y: 'f^car. ('x +['f] 'y = 'y +['f] 'x in 'f^car);
      u4: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x +['f] 'y) *['f] 'z = ('x *['f] 'z) +['f] ('y *['f] 'z) in 'f^car);
      u5: all x: 'f^car. all y: 'f^car. all z: 'f^car. ('x *['f] ('y +['f] 'z) = ('x *['f] 'y) +['f] ('x *['f] 'z) in 'f^car);
      u6: all x: 'f^car. all y: 'f^car. ('x *['f] 'y = 'y *['f] 'x in 'f^car);
      u7: all x: 'f^car. ('f^"1" *['f] 'x = 'x in 'f^car);
      u8: all x: {x: 'f^car | 'x <> 'f^"0" in 'f^car}. (('f^inv 'x) *['f] 'x = 'f^"1" in 'f^car);
      u9: 'f^"0" <> 'f^"1" in 'f^car;
      <J['u]> >- 'C['u] } -->
   sequent { <H>; u: isField{'f}; <J['u]> >- 'C['u] }

interactive field_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in prefield[i:l] } -->
   [main] sequent { <H> >- isField{'f} } -->
   sequent { <H> >- 'f in field[i:l] }

interactive field_equality {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'A = 'B in prefield[i:l] } -->
   [main] sequent { <H> >- isField{'A} } -->
   sequent { <H> >- 'A = 'B in field[i:l] }

interactive field_elim1 {| elim [] |} 'H :
   sequent { <H>; f: prefield[i:l]; u: isField{'f}; <J['f]> >- 'C['f] } -->
   sequent { <H>; f: field[i:l]; <J['f]> >- 'C['f] }

interactive field_elim {| elim [] |} 'H :
   sequent { <H>;
       f: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car; "1": ^car; inv: {x: ^car| 'x <> ^"0" in ^car} -> {x: ^car| 'x <> ^"0" in ^car}};
      u1: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x *['f] 'y) *['f] 'z = 'x *['f] ('y *['f] 'z) in 'f^car);
      u2: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x +['f] 'y) +['f] 'z = 'x +['f] ('y +['f] 'z) in 'f^car);
      v2: all x: 'f^car. ('f^"0" +['f] 'x = 'x in 'f^car);
      w2: all x: 'f^car. ('f^neg 'x) +['f] 'x = 'f^"0" in 'f^car;
      u3: all x: 'f^car. all y: 'f^car. ('x +['f] 'y = 'y +['f] 'x in 'f^car);
      u4: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x +['f] 'y) *['f] 'z = ('x *['f] 'z) +['f] ('y *['f] 'z) in 'f^car);
      u5: all x: 'f^car. all y: 'f^car. all z: 'f^car. ('x *['f] ('y +['f] 'z) = ('x *['f] 'y) +['f] ('x *['f] 'z) in 'f^car);
      u6: all x: 'f^car. all y: 'f^car. ('x *['f] 'y = 'y *['f] 'x in 'f^car);
      u7: all x: 'f^car. ('f^"1" *['f] 'x = 'x in 'f^car);
      u8: all x: {x: 'f^car | 'x <> 'f^"0" in 'f^car}. (('f^inv 'x) *['f] 'x = 'f^"1" in 'f^car);
      u9: 'f^"0" <> 'f^"1" in 'f^car;
      <J['f]> >- 'C['f] } -->
   sequent { <H>; f: field[i:l]; <J['f]> >- 'C['f] }

doc <:doc<
   @begin[doc]
   @modsubsection{Properties}

   @end[doc]
>>
interactive car_wf {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   sequent { <H> >- 'f^car Type }

interactive car_wf2 {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   sequent { <H> >- 'f^car in univ[i:l] }

interactive add_wf {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   sequent { <H> >- 'f^"+" in 'f^car -> 'f^car -> 'f^car }

interactive mul_wf {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   sequent { <H> >- 'f^"*" in 'f^car -> 'f^car -> 'f^car }

interactive neg_wf {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   sequent { <H> >- 'f^neg in 'f^car -> 'f^car }

interactive inv_wf {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   sequent { <H> >- 'f^inv in {x: 'f^car| 'x <> 'f^"0" in 'f^car} -> {x: 'f^car| 'x <> 'f^"0" in 'f^car} }

interactive add_in_car {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   sequent { <H> >- 'a +['f] 'b in 'f^car }

interactive mul_in_car {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   sequent { <H> >- 'a *['f] 'b in 'f^car }

interactive addid_in_car {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   sequent { <H> >- 'f^"0" in 'f^car }

interactive id_in_car {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   sequent { <H> >- 'f^"1" in 'f^car }

interactive neg_in_car {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   sequent { <H> >- 'f^neg 'a in 'f^car }

interactive inv_in_car {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in {x: 'f^car | 'x <> 'f^"0" in 'f^car} } -->
   sequent { <H> >- 'f^inv 'a in 'f^car }

interactive field_add_assoc {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- ('a +['f] 'b) +['f] 'c = 'a +['f] ('b +['f] 'c) in 'f^car }

interactive field_add_assoc2 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- 'a +['f] ('b +['f] 'c) = ('a +['f] 'b) +['f] 'c in 'f^car }

interactive field_mul_assoc {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- ('a *['f] 'b) *['f] 'c = 'a *['f] ('b *['f] 'c) in 'f^car }

interactive field_mul_assoc2 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- 'a *['f] ('b *['f] 'c) = ('a *['f] 'b) *['f] 'c in 'f^car }

interactive field_left_addid {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   sequent { <H> >- 'f^"0" +['f] 'a = 'a in 'f^car }

interactive field_left_addid2 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   sequent { <H> >- 'a = 'f^"0" +['f] 'a in 'f^car }

interactive field_left_id {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   sequent { <H> >- 'f^"1" *['f] 'a = 'a in 'f^car }

interactive field_left_id2 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   sequent { <H> >- 'a = 'f^"1" *['f] 'a in 'f^car }

interactive field_left_neg {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   sequent { <H> >- ('f^neg 'a) +['f] 'a = 'f^"0" in 'f^car }

interactive field_left_neg2 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   sequent { <H> >- 'f^"0" = ('f^neg 'a) +['f] 'a in 'f^car }

interactive field_left_inv {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in {x: 'f^car | 'x <> 'f^"0" in 'f^car} } -->
   sequent { <H> >- ('f^inv 'a) *['f] 'a = 'f^"1" in 'f^car }

interactive field_left_inv2 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in {x: 'f^car | 'x <> 'f^"0" in 'f^car} } -->
   sequent { <H> >- 'f^"1" = ('f^inv 'a) *['f] 'a in 'f^car }

interactive field_add_commut {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   sequent { <H> >- 'a +['f] 'b = 'b +['f] 'a in 'f^car }

interactive field_mul_commut {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   sequent { <H> >- 'a *['f] 'b = 'b *['f] 'a in 'f^car }

interactive field_right_distib {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- ('a +['f] 'b) *['f] 'c = ('a *['f] 'c) +['f] ('b *['f] 'c) in 'f^car }

interactive field_right_distib1 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- ('a *['f] 'c) +['f] ('b *['f] 'c) = ('a +['f] 'b) *['f] 'c in 'f^car }

interactive field_left_distib {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- 'a *['f] ('b +['f] 'c) = ('a *['f] 'b) +['f] ('a *['f] 'c) in 'f^car }

interactive field_left_distib1 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- ('a *['f] 'b) +['f] ('a *['f] 'c) = 'a *['f] ('b +['f] 'c) in 'f^car }

interactive field_0neq1 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   sequent { <H> >- 'f^"0" <> 'f^"1" in 'f^car }

interactive add_eq1 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a = 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- 'a +['f] 'c = 'b +['f] 'c in 'f^car }

interactive add_eq2 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a = 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- 'c +['f] 'a = 'c +['f] 'b in 'f^car }

interactive mul_eq1 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a = 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- 'a *['f] 'c = 'b *['f] 'c in 'f^car }

interactive mul_eq2 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a = 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- 'c *['f] 'a = 'c *['f] 'b in 'f^car }

doc <:doc<
   @begin[doc]
   @modsection{Hierarchy}
   A field is also a ring. If << 'F >> is a field, then << 'F >> is an Abelian group over addition and << carNo0{'F} >> is an Abelian group over multiplication. A field is also an integral domain.

   @end[doc]
>>
define unfold_carNo0 : carNo0{'r} <-->
   rcrd["car":t]{{x: 'r^car|'x <> 'r^"0" in 'r^car}; 'r}
doc docoff

interactive_rw carNo0_rcrd_reduce :
   carNo0{rcrd[a:t]{'x; 'r}} <-->
      eq_label[a:t,"car":t]{  rcrd["car":t]{{u: 'x| 'u <> 'r^"0" in 'x}; 'r};
        eq_label[a:t,"0":t]{  rcrd[a:t]{'x; rcrd["car":t]{{u: 'r^car| 'u <> 'x in 'r^car}; 'r}};
          rcrd[a:t]{'x; carNo0{'r}} }}

let carNo0_rcrd_reduceC = carNo0_rcrd_reduce thenC reduce_eq_label thenC tryC reduce_eq_label

let resource reduce +=
   << carNo0{rcrd[a:t]{'x; 'r}} >>, carNo0_rcrd_reduceC

let inf_carNo0 _ _ _ eqs opt_eqs defs t =
      eqs, opt_eqs, defs, <<group[i:l]>>   (* hack *)

let resource typeinf += (<< carNo0{'r}>>, inf_carNo0)

interactive field_subtype_ring1 {| intro [] |} :
   sequent { <H> >- field[i:l] subtype ring[i:l] }

interactive mul_naddid_naddid1 {| intro [intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   sequent { <H> >- 'a <> 'f^"0" in 'f^car } -->
   sequent { <H> >- 'b <> 'f^"0" in 'f^car } -->
   sequent { <H> >- 'a *['f] 'b <> 'f^"0" in 'f^car }

interactive mul_naddid_naddid2 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in {x: 'f^car|'x <> 'f^"0" in 'f^car} } -->
   [wf] sequent { <H> >- 'b in {x: 'f^car|'x <> 'f^"0" in 'f^car} } -->
   sequent { <H> >- 'a *['f] 'b in {x: 'f^car|'x <> 'f^"0" in 'f^car} }

interactive field_noDiv0 {| intro [intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   sequent { <H> >- noDiv0{'f} }

doc docon
interactive carNo0_car_wf {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   sequent { <H> >- carNo0{'f}^car Type }

interactive carNo0_left_inv {| intro [intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in carNo0{'f}^car } -->
   sequent { <H> >- (carNo0{'f}^inv 'a) *[carNo0{'f}] 'a = carNo0{'f}^"1" in carNo0{'f}^car }

interactive carNo0_left_id {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in carNo0{'f}^car } -->
   sequent { <H> >- carNo0{'f}^"1" *[carNo0{'f}] 'a = 'a in carNo0{'f}^car }

interactive carNo0_assoc {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} field[i:l] :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   [wf] sequent { <H> >- 'a in carNo0{'f}^car } -->
   [wf] sequent { <H> >- 'b in carNo0{'f}^car } -->
   [wf] sequent { <H> >- 'c in carNo0{'f}^car } -->
   sequent { <H> >- ('a *[carNo0{'f}] 'b) *[carNo0{'f}] 'c = 'a *[carNo0{'f}] ('b *[carNo0{'f}] 'c) in carNo0{'f}^car }

interactive field_carNo0_group {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   sequent { <H> >- carNo0{'f} in group[i:l] }

interactive field_carNo0_abelgroup {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   sequent { <H> >- carNo0{'f} in abelg[i:l] }

interactive field_subtype_intDomain {| intro [] |} :
   sequent { <H> >- field[i:l] subtype intDomain[i:l] }

interactive field_subtype_unitring {| intro [] |} :
   sequent { <H> >- field[i:l] subtype unitring[i:l] }

interactive field_subtype_ring {| intro [] |} :
   sequent { <H> >- field[i:l] subtype ring[i:l] }

interactive field_additive_group {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   sequent { <H> >- as_additive{'f} in group[i:l] }

interactive field_additive_abelgroup {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   sequent { <H> >- as_additive{'f} in abelg[i:l] }
doc docoff


(*
(************************************************************************
 * FIELD EXAMPLES                                                        *
 ************************************************************************)
doc <:doc<
   @begin[doc]
   @modsection{Field Examples}

   @end[doc]
>>

doc <:doc<
   @begin[doc]
   @modsubsection{Theorems}

   @end[doc]
>>
*)

(************************************************************************
 * DISPLAY FOfMS                                                        *
 ************************************************************************)

dform field_df1 : except_mode[src] :: except_mode[prl] :: field[i:l] =
   mathbbF `"ield" sub{slot[i:l]}

dform field_df2 : mode[prl] :: field[i:l] =
   `"Field[" slot[i:l] `"]"

dform prefield_df1 : except_mode[src] :: except_mode[prl] :: prefield[i:l] =
   `"prefield" sub{slot[i:l]}

dform prefield_df2 : mode[prl] :: prefield[i:l] =
   `"prefield[" slot[i:l] `"]"

dform isField_df : except_mode[src] :: isField{'f} =
   `"isField(" slot{'f} `")"

dform carNo0_df : except_mode[src] :: carNo0{'r} =
   slot{'r} `"-{0}"

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
