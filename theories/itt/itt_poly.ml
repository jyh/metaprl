doc <:doc<
   @begin[doc]
   @module[Itt_poly]

   This theory defines polynomials.
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
extends Itt_field2
doc docoff

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
open Itt_field2
open Itt_ring2
open Itt_squash
open Itt_equal
open Itt_subtype
open Itt_record_label
open Itt_nat

let _ =
   show_loading "Loading Itt_poly%t"

(************************************************************************
 * Decidable Equality                                                   *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @modsection{Decidable Equality}
   @modsubsection{Rewrites}

   @end[doc]
>>
define unfold_eqDecidable : eqDecidable{'f} <-->
   all x: 'f^car. all y: 'f^car. "iff"{'x = 'y in 'f^car; "assert"{'f^eq 'x 'y}}
doc docoff

let fold_eqDecidable = makeFoldC << eqDecidable{'f} >> unfold_eqDecidable

(* Rules about eqDecidable *)
doc <:doc<
   @begin[doc]
   @modsection{Well-formedness, Introduction, Elimination}
   @modsubsection{Rewrites}

   @end[doc]
>>
interactive eqDecidable_wf {| intro [] |} :
   sequent { <H> >- 'f^car Type } -->
   sequent { <H>; x: 'f^car; y: 'f^car >- 'f^eq 'x 'y in bool } -->
   sequent { <H> >- eqDecidable{'f} Type }

interactive eqDecidable_intro {| intro [] |} :
   sequent { <H> >- 'f^car Type } -->
   sequent { <H>; x: 'f^car; y: 'f^car >- 'f^eq 'x 'y in bool } -->
   sequent { <H>; x: 'f^car; y: 'f^car; 'x = 'y in 'f^car >- "assert"{'f^eq 'x 'y} } -->
   sequent { <H>; x: 'f^car; y: 'f^car; "assert"{'f^eq 'x 'y} >- 'x = 'y in 'f^car } -->
   sequent { <H> >- eqDecidable{'f} }

interactive eqDecidable_elim {| elim [] |} 'H :
   sequent { <H>; u: all x: 'f^car. all y: 'f^car. "iff"{'x = 'y in 'f^car; "assert"{'f^eq 'x 'y}}; <J['u]> >- 'C['u] } -->
   sequent { <H>; u: eqDecidable{'f}; <J['u]> >- 'C['u] }
doc docoff

(************************************************************************
 * Field with Decidable Equality                                        *
 ************************************************************************)
doc <:doc<
   @begin[doc]
   @modsection{Field with decidable equality}
   @modsubsection{Rewrites}

   @end[doc]
>>
define unfold_prefieldE1 : prefieldE[i:l] <-->
   record["eq":t]{r. ('r^car -> 'r^car -> bool); prefield[i:l]}

define unfold_isFieldE1 : isFieldE{'f} <-->
   isField{'f} & eqDecidable{'f}

define unfold_fieldE1 : fieldE[i:l] <-->
   {f: prefieldE[i:l] | isFieldE{'f}}
doc docoff

let unfold_prefieldE = unfold_prefieldE1 thenC addrC [1] unfold_prefield
let unfold_isFieldE = unfold_isFieldE1 thenC addrC [0] unfold_isField thenC addrC [1] unfold_eqDecidable
let unfold_fieldE = unfold_fieldE1 thenC addrC [0] unfold_prefieldE thenC addrC [1] unfold_isFieldE

let fold_prefieldE1 = makeFoldC << prefieldE[i:l] >> unfold_prefieldE1
let fold_prefieldE = makeFoldC << prefieldE[i:l] >> unfold_prefieldE
let fold_isFieldE1 = makeFoldC << isFieldE{'f} >> unfold_isFieldE1
let fold_isFieldE = makeFoldC << isFieldE{'f} >> unfold_isFieldE
let fold_fieldE1 = makeFoldC << fieldE[i:l] >> unfold_fieldE1
let fold_fieldE = makeFoldC << fieldE[i:l] >> unfold_fieldE

let fieldEDT n = rw unfold_fieldE n thenT dT n

let resource elim +=
   [<<fieldE[i:l]>>, fieldEDT]

doc <:doc<
   @begin[doc]
   @modsubsection{Well-formedness}

   @end[doc]
>>
interactive prefieldE_wf {| intro [] |} :
   sequent { <H> >- prefieldE[i:l] Type }

interactive isFieldE_wf {| intro [] |} :
   sequent { <H> >- isField{'f} Type } -->
   sequent { <H> >- eqDecidable{'f} Type } -->
   sequent { <H> >- isFieldE{'f} Type }

interactive fieldE_wf {| intro [] |} :
   sequent { <H> >- fieldE[i:l] Type }

doc <:doc<
   @begin[doc]
   @modsubsection{Introduction and Elimination}

   @end[doc]
>>
interactive prefieldE_intro {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'f in prefield[i:l] } -->
   sequent { <H> >- 'f in {"eq": 'f^car -> 'f^car -> bool} } -->
   sequent { <H> >- 'f in prefieldE[i:l] }

interactive prefieldE_equality {| intro [complete_unless_member] |} :
   sequent { <H> >- 'A = 'B in prefield[i:l] } -->
   sequent { <H> >- 'A = 'B in {"eq": 'A^car -> 'A^car -> bool} } -->
   sequent { <H> >- 'A = 'B in prefieldE[i:l] }

interactive prefieldE_elim {| elim [] |} 'H :
   sequent { <H>; f: prefield[i:l]; x: 'f^car -> 'f^car -> bool; <J['f^eq:='x]> >- 'C['f^eq:='x] } -->
   sequent { <H>; f: prefieldE[i:l]; <J['f]> >- 'C['f] }
doc docoff

interactive car_prefieldE_wf {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} prefieldE[i:l] :
   sequent { <H> >- 'f in prefieldE[i:l] } -->
   sequent { <H> >- 'f^car Type }

doc <:doc< @doc{ } >>
interactive isFieldE_intro {| intro [AutoMustComplete] |} :
   sequent { <H> >- isField{'f} } -->
   sequent { <H> >- eqDecidable{'f} } -->
   sequent { <H> >- isFieldE{'f} }

interactive isFieldE_elim1 {| elim [] |} 'H :
   sequent { <H>; x: isField{'f}; y: eqDecidable{'f}; <J['x, 'y]> >- 'C['x, 'y] } -->
   sequent { <H>; u: isFieldE{'f}; <J['u]> >- 'C['u] }

interactive isFieldE_elim2 {| elim [] |} 'H :
   sequent { <H>; x: isField{'f}; y: all x: 'f^car. all y: 'f^car. "iff"{'x = 'y in 'f^car; "assert"{'f^eq 'x 'y}}; <J['x, 'y]> >- 'C['x, 'y] } -->
   sequent { <H>; u: isFieldE{'f}; <J['u]> >- 'C['u] }

interactive fieldE_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in prefieldE[i:l] } -->
   [main] sequent { <H> >- isFieldE{'f} } -->
   sequent { <H> >- 'f in fieldE[i:l] }

interactive fieldE_intro1 {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   sequent { <H> >- 'f in {"eq": 'f^car -> 'f^car -> bool} } -->
   sequent { <H> >- eqDecidable{'f} } -->
   sequent { <H> >- 'f in fieldE[i:l] }

interactive fieldE_equality {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'A = 'B in prefieldE[i:l] } -->
   [main] sequent { <H> >- isFieldE{'A} } -->
   sequent { <H> >- 'A = 'B in fieldE[i:l] }

interactive fieldE_elim1 {| elim [] |} 'H :
   sequent { <H>; f: prefieldE[i:l]; u: isFieldE{'f}; <J['f]> >- 'C['f] } -->
   sequent { <H>; f: fieldE[i:l]; <J['f]> >- 'C['f] }
doc docoff

(************************************************************************
 * Polynomials                                                          *
 ************************************************************************)
doc <:doc<
   @begin[doc]
   @modsection{Polynomials}
   @modsubsection{Rewrites}

   @end[doc]
>>
define unfold_isZero : isZero{'a; 'F} <-->
   'F^eq 'a 'F^"0"

define unfold_poly : poly{'F} <-->
   {p: (n: nat * (nat{'n +@ 1} -> 'F^car)) |
       fst{'p} > 0 => "not"{"assert"{isZero{(snd{'p} fst{'p}); 'F}}}}

define unfold_zero_poly : zero_poly{'F} <-->
   (0, lambda{x. 'F^"0"})

define unfold_isZeroPoly : isZeroPoly{'p; 'F} <-->
   band{ (fst{'p} =@ 0); isZero{(snd{'p} 0); 'F} }

define unfold_deg : deg{'p} <-->
   fst{'p}

define unfold_coeff : coeff{'p; 'i; 'F} <-->
   if ('i <@ (fst{'p} +@ 1)) then (snd{'p} 'i) else 'F^"0"

define unfold_normalize : normalize{'p; 'F} <-->
   ind{ fst{'p}; (0, snd{'p}); i,up.
        if isZero{(snd{'p} 'i); 'F}
                then 'up
                else ('i, snd{'p}) }

define unfold_add_const : add_const{'p; 'a; 'F} <-->
   (fst{'p}, lambda{x. if ('x=@0) then (snd{'p} 0 +['F] 'a) else (snd{'p} 'x)})

define unfold_mul_const : mul_const{'p; 'a; 'F} <-->
   if isZero{'a; 'F} then zero_poly{'F}
   else (fst{'p}, lambda{x. (snd{'p} 'x) *['F] 'a})

define unfold_add_poly : add_poly{'p; 'q; 'F} <-->
   normalize{(max{fst{'p}; fst{'q}}, lambda{x. coeff{'p;'x;'F} +['F] coeff{'q;'x;'F}}); 'F}

define unfold_sum : sum{'i; 'j; x.'P['x]; 'F} <-->
   ind{('j -@ 'i); k,down. 'down +['F] 'P['i +@ 'k]; 'P['i]; k,up. 'up +['F] 'P['i +@ 'k] }

define unfold_mul_poly : mul_poly{'p; 'q; 'F} <-->
   if bor{isZeroPoly{'p;'F}; isZeroPoly{'q;'F}} then zero_poly{'F}
   else (fst{'p} +@ fst{'q}, lambda{x. sum{0; 'x; y. (coeff{'p;'y;'F} *['F] coeff{'q;('x-@'y);'F}); 'F}})

declare eval_poly{'p; 'a; 'F}

prim_rw unfold_eval_poly : eval_poly{'p; 'a; 'F} <-->
   ind{ fst{'p}; (snd{'p} 0); k,l.
        (snd{'p} 0) +['F] ('a *['F] eval_poly{(fst{'p} -@ 1, lambda{x. snd{'p} ('x +@ 1)}); 'a; 'F}) }
doc docoff

let fold_poly = makeFoldC << poly{'F} >> unfold_poly
let fold_zero_poly = makeFoldC << zero_poly{'F} >> unfold_zero_poly
let fold_isZero = makeFoldC << isZero{'a; 'F} >> unfold_isZero
let fold_isZeroPoly = makeFoldC << isZeroPoly{'p; 'F} >> unfold_isZeroPoly
let fold_deg = makeFoldC << deg{'p} >> unfold_deg
let fold_coeff = makeFoldC << coeff{'p; 'i; 'F} >> unfold_coeff
let fold_normalize = makeFoldC << normalize{'p; 'F} >> unfold_normalize
let fold_add_const = makeFoldC << add_const{'p; 'a; 'F} >> unfold_add_const
let fold_mul_const = makeFoldC << mul_const{'p; 'a; 'F} >> unfold_mul_const
let fold_add_poly = makeFoldC << add_poly{'p; 'q; 'F} >> unfold_add_poly
let fold_mul_poly = makeFoldC << mul_poly{'p; 'q; 'F} >> unfold_mul_poly
let fold_eval_poly = makeFoldC << eval_poly{'p; 'a; 'F} >> unfold_eval_poly

interactive nat_is_int {| intro[AutoMustComplete] |} :
   [wf] sequent { <H> >- 'a='b in nat} -->
   sequent { <H> >- 'a='b in int}

interactive n_in_Nnplus1 {| intro [] |} :
   [wf] sequent { <H> >- 'n in nat } -->
   sequent { <H> >- 'n in nat{'n +@ 1} }

interactive one_ge_0 {| intro [] |} :
   sequent { <H> >- 1 >= 0 }

interactive a_lt_aplus1 {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- 'a < 'a +@ 1 }

interactive plus1_nat {| intro [] |} :
   [wf] sequent { <H> >- 'n in nat } -->
   sequent { <H> >- ('n +@ 1) in nat }

interactive nat1_elim {| elim [] |} 'H :
   sequent { <H>; x: int; v: 'x = 0 in int; <J['x]> >- 'C['x] }  -->
   sequent { <H>; x: nat{1}; <J['x]> >- 'C['x] }

interactive sub_ge_zero {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- 'a -@ 'b >= 0 }

(************************************************************************
 * REDUCTIONS                                                           *
 ************************************************************************)

interactive_rw reduce_coeff_degree1 {| reduce |} :
   (fst{'p} in int) -->
   coeff{'p; fst{'p}; 'F} <--> (snd{'p} fst{'p})

interactive_rw reduce_coeff_degree2 {| reduce |} :
   ('u in int) -->
   coeff{('u, 'v); 'u; 'F} <--> ('v 'u)

doc <:doc<
   @begin[doc]
   @modsubsection{Well-formedness, Introduction, Elimination}

   @end[doc]
>>
interactive isZero_wf {| intro [] |} :
   [wf] sequent { <H> >- 'a in 'F^car } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H> >- isZero{'a; 'F} in bool }

interactive poly_wf {| intro [] |} :
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H> >- poly{'F} Type }

interactive poly_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'p in n: nat * (nat{'n +@ 1} -> 'F^car) } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H>; 0 < fst{'p} >- "not"{"assert"{isZero{(snd{'p} fst{'p}); 'F}}} } -->
   sequent { <H> >- 'p in poly{'F} }

interactive poly_equality {| intro [AutoMustComplete; complete_unless_member]; eqcd |} :
   [wf] sequent { <H> >- 'p = 'q in n: nat * (nat{'n +@ 1} -> 'F^car) } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H> >- 0 < fst{'p} => "not"{"assert"{isZero{(snd{'p} fst{'p}); 'F}}} } -->
   sequent { <H> >- 'p = 'q in poly{'F} }

interactive poly_elim1 {| elim [] |} 'H :
   sequent { <H>; p: poly{'F}; <J['p]> >- 'F^"0" in 'F^car } -->
   sequent { <H>; p: poly{'F}; <J['p]>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H>; u: nat; v: nat{'u +@ 1} -> 'F^car; 0 < 'u => "not"{"assert"{isZero{('v 'u); 'F}}}; <J['u, 'v]> >- 'C['u, 'v] } -->
   sequent { <H>; p: poly{'F}; <J['p]> >- 'C['p] }

interactive zero_poly_wf {| intro [] |} :
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H> >- zero_poly{'F} in poly{'F} }

interactive isZeroPoly_wf {| intro [] |} :
   [wf] sequent { <H> >- fst{'p} in int } -->
   [wf] sequent { <H> >- isZero{(snd{'p} 0); 'F} in bool } -->
   sequent { <H> >- isZeroPoly{'p; 'F} in bool }

interactive coeff_wf {| intro [] |} :
   [wf] sequent { <H> >- 'p in n: nat * (nat{'n +@ 1} -> 'F^car) } -->
   [wf] sequent { <H> >- 'i in nat } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   sequent { <H> >- coeff{'p; 'i; 'F} in 'F^car }

interactive normalize_wf {| intro [] |} :
   [wf] sequent { <H> >- 'p in n: nat * (nat{'n +@ 1} -> 'F^car) } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H> >- normalize{'p; 'F} in poly{'F} }

interactive add_const_wf {| intro [] |} :
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'a in 'F^car } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x +['F] 'y in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H> >- add_const{'p; 'a; 'F} in poly{'F} }

interactive mul_const_wf {| intro [] |} :
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'a in 'F^car } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x *['F] 'y in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car; "not"{"assert"{isZero{'x; 'F}}}; "not"{"assert"{isZero{'y; 'F}}} >- "not"{"assert"{isZero{'x *['F] 'y; 'F}}} } -->
   sequent { <H> >- mul_const{'p; 'a; 'F} in poly{'F} }

interactive add_poly_wf {| intro [] |} :
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'F^eq 'x 'y in bool } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x +['F] 'y in 'F^car } -->
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   sequent { <H> >- add_poly{'p; 'q; 'F} in poly{'F} }

interactive sum_wf {| intro [] |} :
   [wf] sequent { <H> >- 'i in int } -->
   [wf] sequent { <H> >- 'j in int } -->
   [wf] sequent { <H>; x: int; ('x >= min{'i; 'j}); (max{'i; 'j} >= 'x) >- 'P['x] in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x +['F] 'y in 'F^car } -->
   sequent { <H> >- sum{'i; 'j; x.'P['x]; 'F} in 'F^car }

interactive mulpoly_leading_coeff {| intro [] |} :
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x +['F] 'y in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x *['F] 'y in 'F^car } -->
   [wf] sequent { <H>; x1: 'F^car; y1: 'F^car; x2: 'F^car; y2: 'F^car; 'x1 = 'x2 in 'F^car; 'y1 = 'y2 in 'F^car >- 'x1 +['F] 'y1 = 'x2 +['F] 'y2 in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car; "not"{"assert"{isZero{'x; 'F}}}; "not"{"assert"{isZero{'y; 'F}}} >- "not"{"assert"{isZero{'x *['F] 'y; 'F}}} } -->
   sequent { <H> >- sum{0; (fst{'p} +@ fst{'q}); y. (coeff{'p; 'y; 'F} *['F] coeff{'q; ((fst{'p} +@ fst{'q}) -@ 'y); 'F}); 'F} = coeff{'p; fst{'p}; 'F} *['F] coeff{'q; fst{'q}; 'F} in 'F^car }

interactive mul_poly_wf {| intro [] |} :
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x +['F] 'y in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x *['F] 'y in 'F^car } -->
   [wf] sequent { <H>; x1: 'F^car; y1: 'F^car; x2: 'F^car; y2: 'F^car; 'x1 = 'x2 in 'F^car; 'y1 = 'y2 in 'F^car >- 'x1 +['F] 'y1 = 'x2 +['F] 'y2 in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car; "not"{"assert"{isZero{'x; 'F}}}; "not"{"assert"{isZero{'y; 'F}}} >- "not"{"assert"{isZero{'x *['F] 'y; 'F}}} } -->
   sequent { <H> >- mul_poly{'p; 'q; 'F} in poly{'F} }

(************************************************************************
 * DISPLAY FOfMS                                                        *
 ************************************************************************)

dform fieldE_df1 : except_mode[src] :: except_mode[prl] :: fieldE[i:l] =
   mathbbF `"ieldE" sub{slot[i:l]}

dform fieldE_df2 : mode[prl] :: fieldE[i:l] =
   `"FieldE[" slot[i:l] `"]"

dform prefieldE_df1 : except_mode[src] :: except_mode[prl] :: prefieldE[i:l] =
   `"prefieldE" sub{slot[i:l]}

dform prefieldE_df2 : mode[prl] :: prefieldE[i:l] =
   `"prefieldE[" slot[i:l] `"]"

dform isFieldE_df : except_mode[src] :: isFieldE{'F} =
   `"isFieldE(" slot{'F} `")"

dform eqDecidable_df : except_mode[src] :: eqDecidable{'F} =
   `"eqDecidable(" slot{'F} `")"

dform eq_df1 : except_mode[src] :: except_mode[prl] :: parens :: ('F^eq 'a 'b)
 =
   slot["le"]{'a} `"=" sub{'F} slot["le"]{'b}

dform eq_df2 : mode[prl] :: parens :: ('F^eq 'a 'b) =
   slot["le"]{'a} `" " slot{'F} `".eq " slot["le"]{'b}

dform poly_df : except_mode[src] :: poly{'F} =
   slot{'F} `"[x]"

dform zero_poly_df : except_mode[src] :: zero_poly{'F} =
   `"zero_poly(" slot{'F} `")"

dform isZero_df : except_mode[src] :: isZero{'a; 'F} =
   `"isZero(" slot{'a} `"; " slot{'F} `")"

dform isZeroPoly_df : except_mode[src] :: isZeroPoly{'p; 'F} =
   `"isZeroPoly(" slot{'p} `"; " slot{'F} `")"

dform deg_df : except_mode[src] :: deg{'p} =
   `"deg(" slot{'p} `")"

dform coeff_df : except_mode[src] :: coeff{'p; 'i; 'F} =
   `"coeff(" slot{'p} `"; " slot{'i} `"; " slot{'F} `")"

dform normalize_df : except_mode[src] :: normalize{'p; 'F} =
   `"normalize(" slot{'p} `"; " slot{'F} `")"

dform add_poly_const_df : except_mode[src] :: parens :: "prec"[prec_add] :: add_const{'p; 'a; 'F} =
   slot{'p} sub{'F} `" + " slot{'a}

dform mul_poly_const_df : except_mode[src] :: parens :: "prec"[prec_mul] :: mul_const{'p; 'a; 'F} =
   slot{'p} sub{'F} `" * " slot{'a}

dform add_poly_df : except_mode[src] :: parens :: "prec"[prec_add] :: add_poly{'p; 'q; 'F} =
   slot{'p} sub{'F} `" + " slot{'q} sub{'F}

dform mul_poly_df : except_mode[src] :: parens :: "prec"[prec_mul] :: mul_poly{'p; 'q; 'F} =
   slot{'p} sub{'F} `" * " slot{'q} sub{'F}

dform sum_df1 : except_mode[src] :: except_mode[prl] :: sum{'i; 'j; x.'P; 'F} =
   `"(" Sigma sub{'i} sup{'j} slot{'P} `")" sub{'F}

dform sum_df2 : mode[prl] :: sum{'i; 'j; x.'P; 'F} =
   `"sum" sub{'F} `"(" slot{'i} `"," slot{'j} `"," slot{'P} `")"

dform eval_poly_df : except_mode[src] :: eval_poly{'p; 'a; 'F} =
   slot{'p} sub{'F} `"(" slot{'a} `")"

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
