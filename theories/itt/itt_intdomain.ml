doc <:doc<
   @begin[doc]
   @module[Itt_intdomain]

   This theory defines integral domains.
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
extends Itt_labels
doc docoff

open Lm_debug
open Lm_printf

open Basic_tactics

open Itt_grouplikeobj
open Itt_unitring

let _ =
   show_loading "Loading Itt_intdomain%t"

(************************************************************************
 * INTEGRAL DOMAIN                                                      *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @modsection{Integral Domain}
   @modsubsection{Rewrites}

   @end[doc]
>>
define unfold_noDiv0 : noDiv0{'f} <-->
   all a: 'f^car. all b: 'f^car. ('a <> 'f^"0" in 'f^car & 'b <> 'f^"0" in 'f^car & 'a *['f] 'b = 'f^"0" in 'f^car => "false")

define unfold_isIntDomain1 : isIntDomain{'f} <-->
   isUnitRing{'f} & isCommutative{'f} & ('f^"0" <> 'f^"1" in 'f^car) & noDiv0{'f}

define unfold_intDomain1 : intDomain[i:l] <-->
   {f: preunitring[i:l] | isIntDomain{'f}}
doc docoff

let unfold_isIntDomain = unfold_isIntDomain1 thenC addrC [Subterm 1] unfold_isUnitRing thenC addrC [Subterm 2; Subterm 1] unfold_isCommutative thenC addrC [Subterm 2; Subterm 2; Subterm 2] unfold_noDiv0
let unfold_intDomain = unfold_intDomain1 thenC addrC [Subterm 1] unfold_preunitring thenC addrC [Subterm 2] unfold_isIntDomain

let fold_noDiv0 = makeFoldC << noDiv0{'f} >> unfold_noDiv0
let fold_isIntDomain1 = makeFoldC << isIntDomain{'f} >> unfold_isIntDomain1
let fold_isIntDomain = makeFoldC << isIntDomain{'f} >> unfold_isIntDomain
let fold_intDomain1 = makeFoldC << intDomain[i:l] >> unfold_intDomain1
let fold_intDomain = makeFoldC << intDomain[i:l] >> unfold_intDomain

let intDomainDT n = rw unfold_intDomain n thenT dT n

let resource elim +=
   [<<intDomain[i:l]>>, intDomainDT]

doc <:doc<
   @begin[doc]
   @modsubsection{Well-formedness}

   @end[doc]
>>
interactive noDiv0_wf {| intro [] |} :
   [wf] sequent { <H> >- 'f^"0" in 'f^car} -->
   sequent { <H>; x: 'f^car; y: 'f^car >- 'x *['f] 'y in 'f^car} -->
   sequent { <H> >- noDiv0{'f} Type }

interactive isIntDomain_wf {| intro [] |} :
   [wf] sequent { <H> >- 'f^"0" in 'f^car} -->
   [wf] sequent { <H> >- 'f^"1" in 'f^car} -->
   sequent { <H>; x: 'f^car >- 'f^neg 'x in 'f^car} -->
   sequent { <H>; x: 'f^car; y: 'f^car >- 'x *['f] 'y in 'f^car} -->
   sequent { <H>; x: 'f^car; y: 'f^car >- 'x +['f] 'y in 'f^car} -->
   sequent { <H> >- isIntDomain{'f} Type }

interactive intDomain_wf {| intro [] |} :
   sequent { <H> >- intDomain[i:l] Type }

doc <:doc<
   @begin[doc]
   @modsubsection{Introduction and Elimination}

   @end[doc]
>>
interactive noDiv0_intro {| intro [] |} :
   [wf] sequent { <H> >- 'f^"0" in 'f^car} -->
   sequent { <H>; x: 'f^car; y: 'f^car >- 'x *['f] 'y in 'f^car} -->
   sequent { <H>; x: 'f^car; y: 'f^car; 'x <> 'f^"0" in 'f^car; 'y <> 'f^"0" in 'f^car; 'x *['f] 'y = 'f^"0" in 'f^car >- "false" } -->
   sequent { <H> >- noDiv0{'f} }

interactive noDiv0_elim {| elim [] |} 'H :
   sequent { <H>; x: all a: 'f^car. all b: 'f^car. ('a <> 'f^"0" in 'f^car & 'b <> 'f^"0" in 'f^car & 'a *['f] 'b = 'f^"0" in 'f^car => "false"); <J['x]> >- 'C['x] } -->
   sequent { <H>; x: noDiv0{'f}; <J['x]> >- 'C['x] }

interactive isIntDomain_intro {| intro [AutoMustComplete] |} :
   [main] sequent { <H> >- isUnitRing{'f} } -->
   [main] sequent { <H> >- isCommutative{'f} } -->
   [main] sequent { <H> >- 'f^"0" <> 'f^"1" in 'f^car } -->
   [main] sequent { <H> >- noDiv0{'f} } -->
   sequent { <H> >- isIntDomain{'f} }

interactive isIntDomain_elim1 {| elim [] |} 'H :
   sequent { <H>; u: isIntDomain{'f}; u1: isUnitRing{'f}; u2: isCommutative{'f}; u3: 'f^"0" <> 'f^"1" in 'f^car; u4: noDiv0{'f}; <J['u]> >- 'C['u] } -->
   sequent { <H>; u: isIntDomain{'f}; <J['u]> >- 'C['u] }

interactive isIntDomain_elim {| elim [] |} 'H :
   sequent { <H>; u: isIntDomain{'f};
      u1: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x *['f] 'y) *['f] 'z = 'x *['f] ('y *['f] 'z) in 'f^car);
      u2: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x +['f] 'y) +['f] 'z = 'x +['f] ('y +['f] 'z) in 'f^car);
      v2: all x: 'f^car. ('f^"0" +['f] 'x = 'x in 'f^car);
      w2: all x: 'f^car. ('f^neg 'x) +['f] 'x = 'f^"0" in 'f^car;
      u3: all x: 'f^car. all y: 'f^car. ('x +['f] 'y = 'y +['f] 'x in 'f^car);
      u4: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x +['f] 'y) *['f] 'z = ('x *['f] 'z) +['f] ('y *['f] 'z) in 'f^car);
      u5: all x: 'f^car. all y: 'f^car. all z: 'f^car. ('x *['f] ('y +['f] 'z) = ('x *['f] 'y) +['f] ('x *['f] 'z) in 'f^car);
      u6: all x: 'f^car. (('f^"1" *['f] 'x = 'x in 'f^car) & ('x *['f] 'f^"1" = 'x in 'f^car));
      u7: all x: 'f^car. all y: 'f^car. ('x *['f] 'y = 'y *['f] 'x in 'f^car);
      u8: 'f^"0" <> 'f^"1" in 'f^car;
      u9: all a: 'f^car. all b: 'f^car. ('a <> 'f^"0" in 'f^car & 'b <> 'f^"0" in 'f^car & 'a *['f] 'b = 'f^"0" in 'f^car => "false");
      <J['u]> >- 'C['u] } -->
   sequent { <H>; u: isIntDomain{'f}; <J['u]> >- 'C['u] }

interactive intDomain_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in preunitring[i:l] } -->
   [main] sequent { <H> >- isIntDomain{'f} } -->
   sequent { <H> >- 'f in intDomain[i:l] }

interactive intDomain_equality {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'A = 'B in preunitring[i:l] } -->
   [main] sequent { <H> >- isIntDomain{'A} } -->
   sequent { <H> >- 'A = 'B in intDomain[i:l] }

interactive intDomain_elim1 {| elim [] |} 'H :
   sequent { <H>; f: preunitring[i:l]; u: isIntDomain{'f}; <J['f]> >- 'C['f] } -->
   sequent { <H>; f: intDomain[i:l]; <J['f]> >- 'C['f] }

interactive intDomain_elim {| elim [] |} 'H :
   sequent { <H>;
       f: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car; "1": ^car};
      u1: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x *['f] 'y) *['f] 'z = 'x *['f] ('y *['f] 'z) in 'f^car);
      u2: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x +['f] 'y) +['f] 'z = 'x +['f] ('y +['f] 'z) in 'f^car);
      v2: all x: 'f^car. ('f^"0" +['f] 'x = 'x in 'f^car);
      w2: all x: 'f^car. ('f^neg 'x) +['f] 'x = 'f^"0" in 'f^car;
      u3: all x: 'f^car. all y: 'f^car. ('x +['f] 'y = 'y +['f] 'x in 'f^car);
      u4: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x +['f] 'y) *['f] 'z = ('x *['f] 'z) +['f] ('y *['f] 'z) in 'f^car);
      u5: all x: 'f^car. all y: 'f^car. all z: 'f^car. ('x *['f] ('y +['f] 'z) = ('x *['f] 'y) +['f] ('x *['f] 'z) in 'f^car);
      u6: all x: 'f^car. (('f^"1" *['f] 'x = 'x in 'f^car) & ('x *['f] 'f^"1" = 'x in 'f^car));
      u7: all x: 'f^car. all y: 'f^car. ('x *['f] 'y = 'y *['f] 'x in 'f^car);
      u8: 'f^"0" <> 'f^"1" in 'f^car;
      u9: all a: 'f^car. all b: 'f^car. ('a <> 'f^"0" in 'f^car & 'b <> 'f^"0" in 'f^car & 'a *['f] 'b = 'f^"0" in 'f^car => "false");
      <J['f]> >- 'C['f] } -->
   sequent { <H>; f: intDomain[i:l]; <J['f]> >- 'C['f] }

doc <:doc<
   @begin[doc]
   @modsubsection{Properties}

   @end[doc]
>>
interactive car_wf {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   sequent { <H> >- 'f^car Type }

interactive car_wf2 {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   sequent { <H> >- 'f^car in univ[i:l] }

interactive add_wf {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   sequent { <H> >- 'f^"+" in 'f^car -> 'f^car -> 'f^car }

interactive mul_wf {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   sequent { <H> >- 'f^"*" in 'f^car -> 'f^car -> 'f^car }

interactive neg_wf {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   sequent { <H> >- 'f^neg in 'f^car -> 'f^car }

interactive add_in_car {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   sequent { <H> >- 'a in 'f^car } -->
   sequent { <H> >- 'b in 'f^car } -->
   sequent { <H> >- 'a +['f] 'b in 'f^car }

interactive mul_in_car {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   sequent { <H> >- 'a *['f] 'b in 'f^car }

interactive addid_in_car {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   sequent { <H> >- 'f^"0" in 'f^car }

interactive id_in_car {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   sequent { <H> >- 'f^"1" in 'f^car }

interactive neg_in_car {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   sequent { <H> >- 'f^neg 'a in 'f^car }

interactive intDomain_add_assoc {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- ('a +['f] 'b) +['f] 'c = 'a +['f] ('b +['f] 'c) in 'f^car }

interactive intDomain_add_assoc2 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- 'a +['f] ('b +['f] 'c) = ('a +['f] 'b) +['f] 'c in 'f^car }

interactive intDomain_mul_assoc {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- ('a *['f] 'b) *['f] 'c = 'a *['f] ('b *['f] 'c) in 'f^car }

interactive intDomain_mul_assoc2 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- 'a *['f] ('b *['f] 'c) = ('a *['f] 'b) *['f] 'c in 'f^car }

interactive intDomain_left_addid {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   sequent { <H> >- 'f^"0" +['f] 'a = 'a in 'f^car }

interactive intDomain_left_addid2 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   sequent { <H> >- 'a = 'f^"0" +['f] 'a in 'f^car }

interactive intDomain_left_id {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   sequent { <H> >- 'f^"1" *['f] 'a = 'a in 'f^car }

interactive intDomain_left_id2 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   sequent { <H> >- 'a = 'f^"1" *['f] 'a in 'f^car }

interactive intDomain_left_neg {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   sequent { <H> >- ('f^neg 'a) +['f] 'a = 'f^"0" in 'f^car }

interactive intDomain_left_neg2 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   sequent { <H> >- 'f^"0" = ('f^neg 'a) +['f] 'a in 'f^car }

interactive intDomain_add_commut {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   sequent { <H> >- 'a +['f] 'b = 'b +['f] 'a in 'f^car }

interactive intDomain_mul_commut {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   sequent { <H> >- 'a *['f] 'b = 'b *['f] 'a in 'f^car }

interactive intDomain_right_distib {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- ('a +['f] 'b) *['f] 'c = ('a *['f] 'c) +['f] ('b *['f] 'c) in 'f^car }

interactive intDomain_right_distib1 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- ('a *['f] 'c) +['f] ('b *['f] 'c) = ('a +['f] 'b) *['f] 'c in 'f^car }

interactive intDomain_left_distib {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- 'a *['f] ('b +['f] 'c) = ('a *['f] 'b) +['f] ('a *['f] 'c) in 'f^car }

interactive intDomain_left_distib1 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- ('a *['f] 'b) +['f] ('a *['f] 'c) = 'a *['f] ('b +['f] 'c) in 'f^car }

interactive intDomain_0neq1 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   sequent { <H> >- 'f^"0" <> 'f^"1" in 'f^car }

interactive intDomain_noDiv0 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   sequent { <H> >- noDiv0{'f} }

interactive add_eq1 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a = 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- 'a +['f] 'c = 'b +['f] 'c in 'f^car }

interactive add_eq2 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a = 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- 'c +['f] 'a = 'c +['f] 'b in 'f^car }

interactive mul_eq1 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a = 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- 'a *['f] 'c = 'b *['f] 'c in 'f^car }

interactive mul_eq2 {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a = 'b in 'f^car } -->
   [wf] sequent { <H> >- 'c in 'f^car } -->
   sequent { <H> >- 'c *['f] 'a = 'c *['f] 'b in 'f^car }

doc <:doc<
   @begin[doc]
   @modsection{Hierarchy}
   An integral domain is a ring, and also a unit ring.

   @end[doc]
>>
interactive intDomain_subtype_unitring {| intro [] |} :
   sequent { <H> >- intDomain[i:l] subtype unitring[i:l] }

interactive intDomain_subtype_ring {| intro [] |} :
   sequent { <H> >- intDomain[i:l] subtype ring[i:l] }

interactive intDomain_additive_group {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   sequent { <H> >- as_additive{'f} in group[i:l] }

interactive intDomain_additive_abelgroup {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   sequent { <H> >- as_additive{'f} in abelg[i:l] }
doc docoff

interactive intdomain_noDiv02 {| intro [intro_typeinf <<'f>>] |} intDomain[i:l] :
   [wf] sequent { <H> >- 'f in intDomain[i:l] } -->
   [wf] sequent { <H> >- 'a in 'f^car } -->
   [wf] sequent { <H> >- 'b in 'f^car } -->
   sequent { <H> >- 'a <> 'f^"0" in 'f^car } -->
   sequent { <H> >- 'b <> 'f^"0" in 'f^car } -->
   sequent { <H> >- 'a *['f] 'b <> 'f^"0" in 'f^car }

(************************************************************************
 * INTEGRAL DOMAIN EXAMPLES                                             *
 ************************************************************************)
doc <:doc<
   @begin[doc]
   @modsection{Integral Domain Examples}

   @end[doc]
>>
interactive int_noDiv0 {| intro [] |}:
   [wf] sequent { <H> >- 'x in int } -->
   [wf] sequent { <H> >- 'y in int } -->
   [wf] sequent { <H> >- 'x *@ 'y = 0 in int } -->
   sequent { <H> >- 'x = 0 in int or 'y = 0 in int }

interactive int_intdomain {| intro [] |}:
   sequent { <H> >- {car=int; "*"=lambda{x. lambda{y. 'x *@ 'y}}; "+"=lambda{x. lambda{y. 'x +@ 'y}}; "0"=0; neg=lambda{x. (-'x)}; "1"=1} in intDomain[i:l] }

(*
(************************************************************************
 * THEOREMS                                                             *
 ************************************************************************)
doc <:doc<
   @begin[doc]
   @modsubsection{Theorems}

   @end[doc]
>>
*)

(************************************************************************
 * DISPLAY FOfMS                                                        *
 ************************************************************************)

dform intDomain_df1 : except_mode[src] :: except_mode[prl] :: intDomain[i:l] =
   mathbbI `"ntDomain" sub{slot[i:l]}

dform intDomain_df2 : mode[prl] :: intDomain[i:l] =
   `"IntDomain[" slot[i:l] `"]"

dform isIntDomain_df : except_mode[src] :: isIntDomain{'f} =
   `"isIntDomain(" slot{'f} `")"

dform noDiv0_df : except_mode[src] :: noDiv0{'f} =
   `"noDiv0(" slot{'f} `")"
(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
