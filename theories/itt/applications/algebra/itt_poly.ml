doc <:doc<
   @module[Itt_poly]

   This theory defines polynomials.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2004-2006 MetaPRL Group

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
extends Itt_cyclic_group
extends Itt_labels
doc docoff

open Basic_tactics

open Itt_grouplikeobj
open Itt_group
open Itt_equal

(************************************************************************
 * Polynomials                                                          *
 ************************************************************************)
doc <:doc<
   @modsection{Polynomials}
   @modsubsection{Rewrites}

>>
define unfold_isZero : isZero{'a; 'F} <-->
   'F^eq 'a 'F^"0"

define unfold_poly : poly{'F} <-->
   {p: (n: nat * (nat{'n +@ 1} -> 'F^car)) |
       fst{'p} > 0 => "not"{"assert"{isZero{(snd{'p} fst{'p}); 'F}}}}

define unfold_zero_poly : zero_poly{'F} <-->
   (0, lambda{x. 'F^"0"})

define unfold_unit_poly : unit_poly{'F} <-->
   (0, lambda{x. 'F^"1"})

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

interactive_rw unfold_normalize1 : normalize{('u, 'v); 'F} <-->
   ind{ 'u; (0, 'v); i,up.
        if isZero{('v 'i); 'F}
                then 'up
                else ('i, 'v) }

define unfold_add_const : add_const{'p; 'a; 'F} <-->
   (fst{'p}, lambda{x. if ('x=@0) then (snd{'p} 0 +['F] 'a) else (snd{'p} 'x)})

define unfold_mul_const : mul_const{'p; 'a; 'F} <-->
   if isZero{'a; 'F} then zero_poly{'F}
   else (fst{'p}, lambda{x. (snd{'p} 'x) *['F] 'a})

define unfold_add_poly : add_poly{'p; 'q; 'F} <-->
   normalize{(max{fst{'p}; fst{'q}}, lambda{x. coeff{'p;'x;'F} +['F] coeff{'q;'x;'F}}); 'F}

define unfold_neg_poly : neg_poly{'p; 'F} <-->
   (fst{'p}, lambda{x. ('F^neg (snd{'p} 'x))})

define unfold_sum : sum{'i; 'j; x.'P['x]; 'F} <-->
   ind{('j -@ 'i); k,down. 'down +['F] 'P['i +@ 'k]; 'P['i]; k,up. 'up +['F] 'P['i +@ 'k] }

define unfold_mul_poly : mul_poly{'p; 'q; 'F} <-->
   if bor{isZeroPoly{'p;'F}; isZeroPoly{'q;'F}} then zero_poly{'F}
   else normalize{(fst{'p} +@ fst{'q}, lambda{x. sum{0; 'x; y. (coeff{'p;'y;'F} *['F] coeff{'q;('x-@'y);'F}); 'F}}); 'F}

(*define unfold_eval_poly : eval_poly{'p; 'a; 'F} <-->
   ind{ fst{'p}; (snd{'p} fst{'p}); i,up.
        ((snd{'p} (fst{'p} -@ 'i)) +['F] ('a *['F] 'up)) }

interactive_rw unfold_eval_poly1 : eval_poly{('u, 'v); 'a; 'F} <-->
   ind{ 'u; ('v 'u); i,up.
        (('v ('u -@ 'i)) +['F] ('a *['F] 'up)) }
*)
define unfold_eval_poly : eval_poly{'p; 'a; 'F} <-->
   ind{ fst{'p}; (snd{'p} 0); k,up.
        ('up +['F] (natpower{'F; 'a; 'k} *['F] (snd{'p} 'k))) }

interactive_rw unfold_eval_poly1 : eval_poly{('u, 'v); 'a; 'F} <-->
   ind{ 'u; ('v 0); k,up.
        ('up +['F] (natpower{'F; 'a; 'k} *['F] ('v 'k))) }

define unfold_eq_poly : eq_poly{'p; 'q; 'F} <-->
   band{ (fst{'p} =@ fst{'q});
         ind{fst{'p}; 'F^eq (snd{'p} 0) (snd{'q} 0); k, up. band{'up; 'F^eq (snd{'p} 'k) (snd{'q} 'k)}}}
doc docoff

let fold_poly = makeFoldC << poly{'F} >> unfold_poly
let fold_zero_poly = makeFoldC << zero_poly{'F} >> unfold_zero_poly
let fold_unit_poly = makeFoldC << unit_poly{'F} >> unfold_unit_poly
let fold_isZero = makeFoldC << isZero{'a; 'F} >> unfold_isZero
let fold_isZeroPoly = makeFoldC << isZeroPoly{'p; 'F} >> unfold_isZeroPoly
let fold_deg = makeFoldC << deg{'p} >> unfold_deg
let fold_coeff = makeFoldC << coeff{'p; 'i; 'F} >> unfold_coeff
let fold_normalize = makeFoldC << normalize{'p; 'F} >> unfold_normalize
let fold_normalize1 = makeFoldC << normalize{('u, 'v); 'F} >> unfold_normalize1
let fold_add_const = makeFoldC << add_const{'p; 'a; 'F} >> unfold_add_const
let fold_mul_const = makeFoldC << mul_const{'p; 'a; 'F} >> unfold_mul_const
let fold_add_poly = makeFoldC << add_poly{'p; 'q; 'F} >> unfold_add_poly
let fold_neg_poly = makeFoldC << neg_poly{'p; 'F} >> unfold_neg_poly
(*let fold_sum = makeFoldC << sum{'i; 'j; x.'P['x]; 'F} >> unfold_sum*)
let fold_mul_poly = makeFoldC << mul_poly{'p; 'q; 'F} >> unfold_mul_poly
let fold_eval_poly = makeFoldC << eval_poly{'p; 'a; 'F} >> unfold_eval_poly
let fold_eval_poly1 = makeFoldC << eval_poly{('u, 'v); 'a; 'F} >> unfold_eval_poly1
let fold_eq_poly = makeFoldC << eq_poly{'p; 'q; 'F} >> unfold_eq_poly

interactive nat_is_int {| intro[AutoMustComplete]; nth_hyp |} :
   [wf] sequent { <H> >- 'a='b in nat} -->
   sequent { <H> >- 'a='b in int}

interactive n_in_Nnplus1 {| intro []; nth_hyp |} :
   [wf] sequent { <H> >- 'n in nat } -->
   sequent { <H> >- 'n in nat{'n +@ 1} }

interactive one_ge_0 {| intro [] |} :
   sequent { <H> >- 1 >= 0 }

interactive a_lt_aplus1 {| intro []; nth_hyp |} :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- 'a < 'a +@ 1 }

interactive plus1_nat {| intro []; nth_hyp |} :
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
   (fst{'p} in nat) -->
   coeff{'p; fst{'p}; 'F} <--> (snd{'p} fst{'p})

interactive_rw reduce_coeff_0 {| reduce |} :
   ('p in poly{'F}) -->
   coeff{'p; 0; 'F} <--> (snd{'p} 0)

interactive_rw reduce_coeff_degree2 {| reduce |} :
   ('u in nat) -->
   coeff{('u, 'v); 'u; 'F} <--> ('v 'u)

interactive_rw reduce_coeff_zeropoly1 :
   ('n in nat) -->
   coeff{(0, lambda{x. 'F^"0"}); 'n; 'F} <--> ('F^"0")

let coeffZeropolyC = reduce_coeff_zeropoly1

interactive_rw reduce_coeff_zeropoly2 :
   ('n in nat) -->
   coeff{zero_poly{'F}; 'n; 'F} <--> ('F^"0")

let coeffZeropoly1C = reduce_coeff_zeropoly2

interactive_rw reduce_eval_0 {| reduce |} :
   eval_poly{(0, 'v); 'a; 'F} <--> ('v 0)

let resource reduce +=
   << normalize{(0,'v); 'F} >>, wrap_reduce unfold_normalize

doc <:doc<
   @modsubsection{Well-formedness, Introduction, Elimination}

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

interactive poly_univ {| intro [] |} :
   [wf] sequent { <H> >- 'F^car in univ[i:l] } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H> >- poly{'F} in univ[i:l] }

interactive poly_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'p in n: nat * (nat{'n +@ 1} -> 'F^car) } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H>; 0 < fst{'p} >- "not"{"assert"{isZero{(snd{'p} fst{'p}); 'F}}} } -->
   sequent { <H> >- 'p in poly{'F} }

interactive poly_equality {| intro [AutoMustComplete; complete_unless_member] |} :
   [wf] sequent { <H> >- 'p = 'q in n: nat * (nat{'n +@ 1} -> 'F^car) } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H> >- 0 < fst{'p} => "not"{"assert"{isZero{(snd{'p} fst{'p}); 'F}}} } -->
   sequent { <H> >- 'p = 'q in poly{'F} }

interactive poly_elim1 {| elim [] |} 'H :
   [wf] sequent { <H>; p: poly{'F}; <J['p]> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; p: poly{'F}; <J['p]>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H>; u: nat; v: nat{'u +@ 1} -> 'F^car; 0 < 'u => "not"{"assert"{isZero{('v 'u); 'F}}}; <J['u, 'v]> >- 'C['u, 'v] } -->
   sequent { <H>; p: poly{'F}; <J['p]> >- 'C['p] }

interactive zero_poly_wf {| intro [] |} :
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H> >- zero_poly{'F} in poly{'F} }

interactive unit_poly_wf {| intro [] |} :
   [wf] sequent { <H> >- 'F^"1" in 'F^car } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H> >- unit_poly{'F} in poly{'F} }

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

interactive normalize_fst_wf {| intro [] |} :
   [wf] sequent { <H> >- 'p in n: nat * (nat{'n +@ 1} -> 'F^car) } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H> >- fst{normalize{'p; 'F}} in int }

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

interactive neg_poly_wf {| intro [] |} :
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'F^eq 'x 'y in bool } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^neg 'x in 'F^car } -->
   sequent { <H>; x: 'F^car; "not"{"assert"{isZero{'x; 'F}}}; "assert"{isZero{'F^neg 'x; 'F}} >- "false" } -->
   sequent { <H> >- neg_poly{'p; 'F} in poly{'F} }

interactive sum_wf {| intro [] |} :
   [wf] sequent { <H> >- 'i in int } -->
   [wf] sequent { <H> >- 'j in int } -->
   [wf] sequent { <H>; x: int; ('x >= min{'i; 'j}); (max{'i; 'j} >= 'x) >- 'P['x] in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x +['F] 'y in 'F^car } -->
   sequent { <H> >- sum{'i; 'j; x.'P['x]; 'F} in 'F^car }

interactive mul_poly_wf {| intro [] |} :
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x +['F] 'y in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x *['F] 'y in 'F^car } -->
   sequent { <H> >- mul_poly{'p; 'q; 'F} in poly{'F} }

interactive eval_poly_wf {| intro [] |} :
   [wf] sequent { <H> >- 'p in n: nat * (nat{'n +@ 1} -> 'F^car) } -->
   [wf] sequent { <H> >- 'a in 'F^car } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H> >- 'F^"1" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x +['F] 'y in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x *['F] 'y in 'F^car } -->
   sequent { <H> >- eval_poly{'p; 'a; 'F} in 'F^car }

interactive eq_poly_wf {| intro [] |} :
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'q in poly{'F} } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'F^eq 'x 'y in bool } -->
   sequent { <H> >- eq_poly{'p; 'q; 'F} in bool }

doc <:doc<
   @modsubsection{Properties}

>>
interactive poly_normalize {| intro [] |} :
   [wf] sequent { <H> >- 'p in poly{'F} } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H> >- normalize{'p; 'F} = 'p in poly{'F} }

interactive eval_leadingcoeff_isZero {| intro [] |} :
   [wf] sequent { <H> >- 'p in n: nat * (nat{'n +@ 1} -> 'F^car) } -->
   [wf] sequent { <H> >- 'a in 'F^car } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H> >- 'F^"1" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x +['F] 'y in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x *['F] 'y in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car; "assert"{isZero{'y; 'F}} >- "assert"{isZero{'x *['F] 'y; 'F}} } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car; "assert"{isZero{'y; 'F}} >- 'x +['F] 'y = 'x in 'F^car } -->
   [wf] sequent { <H> >- fst{'p} > 0 } -->
   sequent { <H> >- "assert"{isZero{(snd{'p} fst{'p}); 'F}} } -->
   sequent { <H> >- eval_poly{'p; 'a; 'F} = eval_poly{((fst{'p} -@ 1), snd{'p}); 'a; 'F} in 'F^car }

interactive eval_leadingcoeff_isZero1 {| intro [] |} :
   [wf] sequent { <H> >- 'u in nat } -->
   [wf] sequent { <H> >- 'v in (nat{'u +@ 2} -> 'F^car) } -->
   [wf] sequent { <H> >- 'a in 'F^car } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H> >- 'F^"1" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x +['F] 'y in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x *['F] 'y in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car; "assert"{isZero{'y; 'F}} >- "assert"{isZero{'x *['F] 'y; 'F}} } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car; "assert"{isZero{'y; 'F}} >- 'x +['F] 'y = 'x in 'F^car } -->
   sequent { <H> >- "assert"{isZero{('v ('u +@ 1)); 'F}} } -->
   sequent { <H> >- eval_poly{('u +@ 1, 'v); 'a; 'F} = eval_poly{('u, 'v); 'a; 'F} in 'F^car }

interactive eval_normalize {| intro [] |} :
   [wf] sequent { <H> >- 'p in n: nat * (nat{'n +@ 1} -> 'F^car) } -->
   [wf] sequent { <H> >- 'a in 'F^car } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H> >- 'F^"1" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x +['F] 'y in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car >- 'x *['F] 'y in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car; "assert"{isZero{'y; 'F}} >- "assert"{isZero{'x *['F] 'y; 'F}} } -->
   [wf] sequent { <H>; x: 'F^car; y: 'F^car; "assert"{isZero{'y; 'F}} >- 'x +['F] 'y = 'x in 'F^car } -->
   sequent { <H> >- eval_poly{normalize{'p; 'F}; 'a; 'F} = eval_poly{'p; 'a; 'F} in 'F^car }

interactive normalize_leadingcoeff1 {| intro [] |} :
   [wf] sequent { <H> >- 'p in n: nat * (nat{'n +@ 1} -> 'F^car) } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H> >- fst{normalize{'p; 'F}} < fst{'p} +@ 1 }

interactive normalize_leadingcoeff2 {| intro [] |} :
   [wf] sequent { <H> >- 'u in nat } -->
   [wf] sequent { <H> >- 'v in nat{'u +@ 1} -> 'F^car } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H> >- fst{normalize{('u,'v); 'F}} < 'u +@ 1 }

interactive coeff_normalize {| intro [] |} :
   [wf] sequent { <H> >- 'p in n: nat * (nat{'n +@ 1} -> 'F^car) } -->
   [wf] sequent { <H> >- 'i in nat } -->
   [wf] sequent { <H> >- 'F^"0" in 'F^car } -->
   [wf] sequent { <H>; x: 'F^car >- 'F^eq 'x 'F^"0" in bool } -->
   sequent { <H> >- coeff{normalize{'p; 'F}; 'i; 'F} = coeff{'p; 'i; 'F} in 'F^car }

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

doc docoff

(************************************************************************
 * DISPLAY FOfMS                                                        *
 ************************************************************************)

prec prec_neg
prec prec_add

prec prec_add < prec_neg
prec prec_add < prec_mul
prec prec_neg < prec_mul
prec prec_neg < prec_inv

dform poly_df : except_mode[src] :: poly{'F} =
   slot{'F} `"[x]"

dform zero_poly_df : except_mode[src] :: zero_poly{'F} =
   `"zero_poly(" slot{'F} `")"

dform unit_poly_df : except_mode[src] :: unit_poly{'F} =
   `"unit_poly(" slot{'F} `")"

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

dform neg_poly_df : except_mode[src] :: parens :: "prec"[prec_neg] :: neg_poly{'p; 'F} =
   `"-" slot{'p} sub{'F}

dform mul_poly_df : except_mode[src] :: parens :: "prec"[prec_mul] :: mul_poly{'p; 'q; 'F} =
   slot{'p} sub{'F} `" * " slot{'q} sub{'F}

dform sum_df1 : except_mode[src] :: except_mode[prl] :: sum{'i; 'j; x.'P; 'F} =
   `"(" Sigma sub{'i} sup{'j} slot{'P} `")" sub{'F}

dform sum_df2 : mode[prl] :: sum{'i; 'j; x.'P; 'F} =
   `"sum" sub{'F} `"(" slot{'i} `"," slot{'j} `"," slot{'P} `")"

dform eval_poly_df : except_mode[src] :: eval_poly{'p; 'a; 'F} =
   slot{'p} sub{'F} `"(" slot{'a} `")"

dform eq_poly_df : except_mode[src] :: parens :: eq_poly{'p; 'q; 'F} =
   slot{'p} sub{'F} `" eq " slot{'q} sub{'F}

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
