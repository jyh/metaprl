doc <:doc<
   @begin[doc]
   @module[Itt_unitring]

   This theory defines unit rings.
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
doc docoff

open Lm_debug
open Lm_printf

open Basic_tactics

open Itt_ring2
open Itt_equal

let _ =
   show_loading "Loading Itt_unitring%t"

(************************************************************************
 * RING                                                                 *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @modsection{Unit ring}
   @modsubsection{Rewrites}
   A ring with a multiplicative identity is called a ring @emph{with identity}, or sometimes @tt{unit ring}.

   @end[doc]
>>
define unfold_preunitring1 : preunitring[i:l] <-->
   record["1":t]{r. 'r^car; prering[i:l]}

define unfold_isUnitRing1 : isUnitRing{'r} <-->
   isRing{'r} & all x: 'r^car. ('r^"1" *['r] 'x = 'x  in 'r^car & 'x *['r] 'r^"1" = 'x in 'r^car )

define unfold_unitring1 : unitring[i:l] <-->
   {R: preunitring[i:l] | isUnitRing{'R}}
doc docoff

let unfold_preunitring = unfold_preunitring1 thenC addrC [Subterm 2] unfold_prering
let unfold_isUnitRing = unfold_isUnitRing1 thenC addrC [Subterm 1] unfold_isRing
let unfold_unitring = unfold_unitring1 thenC addrC [Subterm 1] unfold_preunitring thenC addrC [Subterm 2] unfold_isUnitRing

let fold_preunitring = makeFoldC << preunitring[i:l] >> unfold_preunitring
let fold_isUnitRing1 = makeFoldC << isUnitRing{'R} >> unfold_isUnitRing1
let fold_isUnitRing = makeFoldC << isUnitRing{'R} >> unfold_isUnitRing
let fold_unitring1 = makeFoldC << unitring[i:l] >> unfold_unitring1
let fold_unitring = makeFoldC << unitring[i:l] >> unfold_unitring

doc <:doc<
   @begin[doc]
   @modsubsection{Well-formedness}

   @end[doc]
>>
interactive preunitring_wf {| intro [] |} :
   sequent { <H> >- preunitring[i:l] Type }

interactive isUnitRing_wf {| intro [] |} :
   [wf] sequent { <H> >- 'R^"0" in 'R^car} -->
   [wf] sequent { <H> >- 'R^"1" in 'R^car} -->
   [wf] sequent { <H>; x: 'R^car >- 'R^neg 'x in 'R^car} -->
   [wf] sequent { <H>; x: 'R^car; y: 'R^car >- 'x *['R] 'y in 'R^car} -->
   [wf] sequent { <H>; x: 'R^car; y: 'R^car >- 'x +['R] 'y in 'R^car} -->
   sequent { <H> >- isUnitRing{'R} Type }

interactive unitring_wf {| intro [] |} :
   sequent { <H> >- unitring[i:l] Type }

doc <:doc<
   @begin[doc]
   @modsubsection{Introduction and Elimination}

   @end[doc]
>>
interactive preunitring_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'R in {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car; "1": ^car} } -->
   sequent { <H> >- 'R in preunitring[i:l] }

interactive preunitring_equality {| intro [complete_unless_member] |} :
   [wf] sequent { <H> >- 'A = 'B in {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car; "1": ^car} } -->
   sequent { <H> >- 'A = 'B in preunitring[i:l] }

interactive preunitring_elim {| elim [] |} 'H :
   sequent { <H>; R: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car; "1": ^car}; <J['R]> >- 'C['R] } -->
   sequent { <H>; R: preunitring[i:l]; <J['R]> >- 'C['R] }
doc docoff

interactive car_preunitring_wf {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} preunitring[i:l] :
   [wf] sequent { <H> >- 'R in preunitring[i:l] } -->
   sequent { <H> >- 'R^car Type }

doc docon
interactive isUnitRing_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'R^car Type } -->
   [main] sequent { <H> >- isRing{'R} } -->
   [wf] sequent { <H>; x: 'R^car >- 'R^"1" *['R] 'x = 'x in 'R^car } -->
   [wf] sequent { <H>; x: 'R^car >- 'x *['R] 'R^"1" = 'x in 'R^car } -->
   sequent { <H> >- isUnitRing{'R} }

interactive isUnitRing_elim1 {| elim [] |} 'H :
   sequent { <H>; u: isUnitRing{'R}; u1: isRing{'R}; u2: all x: 'R^car. ('R^"1" *['R] 'x = 'x  in 'R^car & 'x *['R] 'R^"1" = 'x in 'R^car); <J['u]> >- 'C['u] } -->
   sequent { <H>; u: isUnitRing{'R}; <J['u]> >- 'C['u] }

interactive isUnitRing_elim {| elim [] |} 'H :
   sequent { <H>; u: isUnitRing{'R};
      u1: all x: 'R^car. all y: 'R^car. all z: 'R^car. (('x *['R] 'y) *['R] 'z = 'x *['R] ('y *['R] 'z) in 'R^car);
      u2: all x: 'R^car. all y: 'R^car. all z: 'R^car. (('x +['R] 'y) +['R] 'z = 'x +['R] ('y +['R] 'z) in 'R^car);
      v2: all x: 'R^car. ('R^"0" +['R] 'x = 'x in 'R^car);
      w2: all x: 'R^car. ('R^neg 'x) +['R] 'x = 'R^"0" in 'R^car;
      u3: all x: 'R^car. all y: 'R^car. ('x +['R] 'y = 'y +['R] 'x in 'R^car);
      u4: all x: 'R^car. all y: 'R^car. all z: 'R^car. (('x +['R] 'y) *['R] 'z = ('x *['R] 'z) +['R] ('y *['R] 'z) in 'R^car);
      u5: all x: 'R^car. all y: 'R^car. all z: 'R^car. ('x *['R] ('y +['R] 'z) = ('x *['R] 'y) +['R] ('x *['R] 'z) in 'R^car);
      u6: all x: 'R^car. (('R^"1" *['R] 'x = 'x in 'R^car) & ('x *['R] 'R^"1" = 'x in 'R^car));
      <J['u]> >- 'C['u] } -->
   sequent { <H>; u: isUnitRing{'R}; <J['u]> >- 'C['u] }

interactive unitring_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'R in preunitring[i:l] } -->
   [main] sequent { <H> >- isUnitRing{'R} } -->
   sequent { <H> >- 'R in unitring[i:l] }

interactive unitring_equality {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'A = 'B in preunitring[i:l] } -->
   sequent { <H> >- isUnitRing{'A} } -->
   sequent { <H> >- 'A = 'B in unitring[i:l] }

interactive unitring_elim1 {| elim [] |} 'H :
   sequent { <H>; R: preunitring[i:l]; u: isUnitRing{'R}; <J['R]> >- 'C['R] } -->
   sequent { <H>; R: unitring[i:l]; <J['R]> >- 'C['R] }

interactive unitring_elim {| elim [] |} 'H :
   sequent { <H>; R: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car; "1": ^car};
      u1: all x: 'R^car. all y: 'R^car. all z: 'R^car. (('x *['R] 'y) *['R] 'z = 'x *['R] ('y *['R] 'z) in 'R^car);
      u2: all x: 'R^car. all y: 'R^car. all z: 'R^car. (('x +['R] 'y) +['R] 'z = 'x +['R] ('y +['R] 'z) in 'R^car);
      v2: all x: 'R^car. ('R^"0" +['R] 'x = 'x in 'R^car);
      w2: all x: 'R^car. ('R^neg 'x) +['R] 'x = 'R^"0" in 'R^car;
      u3: all x: 'R^car. all y: 'R^car. ('x +['R] 'y = 'y +['R] 'x in 'R^car);
      u4: all x: 'R^car. all y: 'R^car. all z: 'R^car. (('x +['R] 'y) *['R] 'z = ('x *['R] 'z) +['R] ('y *['R] 'z) in 'R^car);
      u5: all x: 'R^car. all y: 'R^car. all z: 'R^car. ('x *['R] ('y +['R] 'z) = ('x *['R] 'y) +['R] ('x *['R] 'z) in 'R^car);
      u6: all x: 'R^car. (('R^"1" *['R] 'x = 'x in 'R^car) & ('x *['R] 'R^"1" = 'x in 'R^car));
      <J['R]> >- 'C['R] } -->
   sequent { <H>; R: unitring[i:l]; <J['R]> >- 'C['R] }

doc <:doc<
   @begin[doc]
   @modsection{Hierarchy}
   A unit ring is a ring and a monoid.

   @end[doc]
>>
interactive unitring_subtype_ring {| intro [] |} :
   sequent { <H> >- unitring[i:l] subtype ring[i:l] }

interactive unitring_subtype_monoid {| intro [] |} :
   sequent { <H> >- unitring[i:l] subtype monoid[i:l] }
doc docoff

interactive car_unitring_wf {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitring[i:l] :
   [wf] sequent { <H> >- 'R in unitring[i:l] } -->
   sequent { <H> >- 'R^car Type }

interactive car_unitring_wf2 {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'R in unitring[i:l] } -->
   sequent { <H> >- 'R^car in univ[i:l] }

interactive unitring_mul {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitring[i:l] :
   [wf] sequent { <H> >- 'R in unitring[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'b in 'R^car } -->
   sequent { <H> >- 'a *['R] 'b in 'R^car }

interactive unitring_mul_assoc {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitring[i:l] :
   [wf] sequent { <H> >- 'R in unitring[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'b in 'R^car } -->
   [wf] sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- ('a *['R] 'b) *['R] 'c = 'a *['R] ('b *['R] 'c) in 'R^car }

interactive unitring_mul_assoc2 {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitring[i:l] :
   [wf] sequent { <H> >- 'R in unitring[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'b in 'R^car } -->
   [wf] sequent { <H> >- 'c in 'R^car } -->
   sequent { <H> >- 'a *['R] ('b *['R] 'c) = ('a *['R] 'b) *['R] 'c in 'R^car }

interactive unitring_id {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitring[i:l] :
   [wf] sequent { <H> >- 'R in unitring[i:l] } -->
   sequent { <H> >- 'R^"1" in 'R^car }

interactive unitring_left_id {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitring[i:l] :
   [wf] sequent { <H> >- 'R in unitring[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'R^"1" *['R] 'a = 'a in 'R^car }

interactive unitring_right_id {| intro [AutoMustComplete; intro_typeinf <<'R>>] |} unitring[i:l] :
   [wf] sequent { <H> >- 'R in unitring[i:l] } -->
   [wf] sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'a *['R] 'R^"1" = 'a in 'R^car }


(************************************************************************
 * UNITS                                                                *
 ************************************************************************)
doc <:doc<
   @begin[doc]
   @modsection{Units}
   An element << 'x >> of the unit ring << 'R >> is a @tt{unit} if there exists an element << 'a >> such that << 'a *['R] 'x = 'R^"1" in 'R^car >> and << 'x *['R] 'a = 'R^"1" in 'R^car >> . This element << 'a >> is uniquely determined by << 'x >> and is called the multiplicative inverse of << 'x >>.

   @end[doc]
>>
define unfold_isUnit : isUnit{'x; 'R} <-->
   exst a: 'R^car. ('a *['R] 'x = 'R^"1" in 'R^car & 'x *['R] 'a = 'R^"1" in 'R^car)

doc <:doc<
   @begin[doc]
   @modsubsection{Well-formedness, Introduction, and Elimination}

   @end[doc]
>>
interactive isUnit_wf {| intro [] |} :
   [wf] sequent { <H>; a: 'R^car >- 'a *['R] 'x in 'R^car } -->
   [wf] sequent { <H>; a: 'R^car >- 'x *['R] 'a in 'R^car } -->
   [wf] sequent { <H> >- 'R^"1" in 'R^car } -->
   sequent { <H> >- isUnit{'x; 'R} Type }

interactive isUnit_univ {| intro [] |} :
   [wf] sequent { <H> >- 'R^car in univ[i:l] } -->
   [wf] sequent { <H>; a: 'R^car >- 'a *['R] 'x in 'R^car } -->
   [wf] sequent { <H>; a: 'R^car >- 'x *['R] 'a in 'R^car } -->
   [wf] sequent { <H> >- 'R^"1" in 'R^car } -->
   sequent { <H> >- isUnit{'x; 'R} in univ[i:l] }

interactive isUnit_intro {| intro [] |} 'a :
   [wf] sequent { <H> >- 'a in 'R^car } -->
   [wf] sequent { <H> >- 'a *['R] 'x = 'R^"1" in 'R^car } -->
   [wf] sequent { <H> >- 'x *['R] 'a = 'R^"1" in 'R^car } -->
   [wf] sequent { <H>; u: 'R^car >- 'u *['R] 'x in 'R^car } -->
   [wf] sequent { <H>; u: 'R^car >- 'x *['R] 'u in 'R^car } -->
   [wf] sequent { <H> >- 'R^"1" in 'R^car } -->
   sequent { <H> >- isUnit{'x; 'R} }

interactive isUnit_elim {| elim [] |} 'H :
   sequent { <H>; y: 'R^car; z: 'y *['R] 'x = 'R^"1" in 'R^car; k: 'x *['R] 'y = 'R^"1" in 'R^car; <J[('y, ('z, 'k))]> >- 'C[('y, ('z, 'k))] } -->
   sequent { <H>; u: isUnit{'x; 'R}; <J['u]> >- 'C['u] }

doc <:doc<
   @begin[doc]
   @modsubsection{Theorems}
   The set of units forms a group under multiplication.

   @end[doc]
>>
interactive unitset_group {| intro [] |} :
   [wf] sequent { <H> >- 'R in unitring[i:l] } -->
   [wf] sequent { <H> >- 'inv in x: {x: 'R^car | isUnit{'x; 'R}} -> isUnit{'x; 'R} } -->
   sequent { <H> >- {car={x: 'R^car| isUnit{'x; 'R}}; "*"='R^"*"; "1"='R^"1"; inv=lambda{x.fst{'inv 'x}}} in group[i:l] }
doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform preunitring_df1 : except_mode[src] :: except_mode[prl] :: preunitring[i:l] =
   `"preunitring" sub{slot[i:l]}

dform preunitring_df2 : mode[prl] :: preunitring[i:l] =
   `"preunitring[" slot[i:l] `"]"

dform isUnitRing_df : except_mode[src] :: isUnitRing{'R} =
   `"isUnitRing(" slot{'R} `")"

dform unitring_df1 : except_mode[src] :: except_mode[prl] :: unitring[i:l] =
   mathbbU `"nitRing" sub{slot[i:l]}

dform unitring_df2 : mode[prl] :: unitring[i:l] =
   `"UnitRing[" slot[i:l] `"]"

dform isUnit_df : except_mode[src] :: isUnit{'x; 'R} =
   `"isUnit(" slot{'x} `"; " slot{'R} `")"

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
