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
define unfold_poly : poly{'f} <-->
   {p: (n: nat * (nat{'n + 1} -> 'f^car)) |
       fst{'p} > 0 => (snd{'p} fst{'p} <> 'f^"0" in 'f^car)}

define unfold_zero_poly : zero_poly{'f} <-->
   (0, lambda{x. 'f^"0"})

define unfold_isZero : isZero{'a; 'f} <-->
   'f^eq 'a 'f^"0"

define unfold_isZeroPoly : isZeroPoly{'p; 'f} <-->
   band{ (fst{'p} =@ 0); isZero{(snd{'p} 0); 'f} }
(*   band{ (fst{'p} =@ 0); 'f^eq (snd{'p} 0) 'f^"0" } *)

define unfold_deg : deg{'p} <-->
   fst{'p}

define unfold_coeff : coeff{'p; 'i; 'f} <-->
   if ('i <=@ fst{'p}) then (snd{'p} 'i) else 'f^"0"

declare normalize{'p; 'f}

prim_rw unfold_normalize : normalize{'p; 'f} <-->
   ind{ fst{'p}; 'p; k,l.
        if isZero{(snd{'p} fst{'p}); 'f}
(*         k,l. if ('f^eq (snd{'p} fst{'p}) 'f^"0") *)
                then normalize{(fst{'p} -@ 1, snd{'p}); 'f}
                else 'p }

define unfold_add_const : add_const{'p; 'a; 'f} <-->
   (fst{'p}, lambda{x. if ('x=@0) then (snd{'p} 0 +['f] 'a) else (snd{'p} 'x)})

define unfold_mul_const : mul_const{'p; 'a; 'f} <-->
   if isZero{'a; 'f} then zero_poly{'f}
(*   if ('f^eq 'a 'f^"0") then zero_poly{'f} *)
   else (fst{'p}, lambda{x. (snd{'p} 'x) *['f] 'a})

define unfold_add : add{'p; 'q; 'f} <-->
   normalize{(max{fst{'p}; fst{'q}}, lambda{x. coeff{'p;'x;'f} +['f] coeff{'q;'x;'f}}); 'f}

declare sum{'i; 'j; x.'P['x]; 'f}

prim_rw unfold_sum : sum{'i; 'j; x.'P['x]; 'f} <-->
   ind{('j -@ 'i); m,n. sum{'i; ('j+@1); x.'P['x]; 'f} +['f] 'P['j]; 'P['i]; k,l. sum{'i; ('j-@1); x.'P['x]; 'f} +['f] 'P['j] }

define unfold_mul : mul{'p; 'q; 'f} <-->
   if bor{isZeroPoly{'p;'f}; isZeroPoly{'q;'f}} then zero_poly{'f}
   else (fst{'p} +@ fst{'q}, lambda{x. sum{0; 'x; y. (coeff{'p;'y;'f} *['f] coeff{'q;('x-@'y);'f}); 'f}})

declare eval_poly{'p; 'a; 'f}

prim_rw unfold_eval_poly : eval_poly{'p; 'a; 'f} <-->
   ind{ fst{'p}; (snd{'p} 0); k,l.
        (snd{'p} 0) +['f] ('a *['f] eval_poly{(fst{'p} -@ 1, lambda{x. snd{'p} ('x +@ 1)}); 'a; 'f}) }