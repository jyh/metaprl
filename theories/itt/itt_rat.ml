doc <:doc<
   @begin[doc]
   @module[Itt_rat]

   Rational numbers axiomatization.

   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 1998 Jason Hickey, Cornell University

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

   Author: Yegor Bryukhov
   @email{ynb@mail.ru}
   @end[license]
>>

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>
extends Itt_equal
extends Itt_squash
extends Itt_rfun
extends Itt_bool
extends Itt_logic
extends Itt_struct
extends Itt_decidable
extends Itt_quotient
extends Itt_nequal
extends Itt_int_arith
extends Itt_field
extends Itt_order
doc <:doc< @docoff >>

open Lm_debug
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp

open Tactic_type.Tacticals
open Top_conversionals
open Dtactic

open Itt_equal
open Itt_struct
open Itt_bool
open Itt_int_base
open Itt_squash
open Itt_int_ext

let _ = show_loading "Loading Itt_rat%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @terms

   @end[doc]
>>

define unfold_posnat :
   posnat <--> ({x:int | 'x>0})

define unfold_int0 :
   int0 <--> ({x:int | 'x<>0})

declare add_rat{'a;'b}
declare mul_rat{'a;'b}
declare neg_rat{'a}
declare inv_rat{'a}
declare lt_bool_rat{'a;'b}
declare le_bool_rat{'a;'b}
declare beq_rat{'a;'b}

define unfold_rat : rat{'a;'b} <--> ('a,'b)

let fold_rat = makeFoldC <<rat{'a;'b}>> unfold_rat

define unfold_rat_of_int :
   rat_of_int{'a} <--> rat{'a; 1}

doc <:doc<
   @begin[doc]
   The basic arithmetic operators are defined with
   the following terms. Basic predicates are boolean.
   @end[doc]
>>

prim_rw reduce_add_rat : add_rat{rat{'a;'b}; rat{'c;'d}} <--> rat{('a *@ 'd) +@ ('c *@ 'b); ('b *@ 'd)}
prim_rw reduce_mul_rat : mul_rat{rat{'a;'b}; rat{'c;'d}} <--> rat{('a *@ 'c); ('b *@ 'd)}
prim_rw reduce_neg_rat : neg_rat{rat{'a;'b}} <--> rat{minus{'a};'b}
prim_rw reduce_lt_bool_rat : lt_bool_rat{rat{'a;'b};rat{'c;'d}} <--> lt_bool{('a *@ 'd);('c *@ 'b)}
prim_rw reduce_le_bool_rat : le_bool_rat{rat{'a;'b};rat{'c;'d}} <--> le_bool{('a *@ 'd);('c *@ 'b)}

prim_rw reduce_inv_rat :
	('a in posnat) -->
	inv_rat{rat{'a;'b}} <--> rat{ (sign{'a} *@ 'b) ; abs{'a}}

prim_rw reduce_beq_rat :
   beq_rat{ ('a,'b) ; ('c,'d) } <--> beq_int{ ('a *@ 'd) ; ('c *@ 'b) }

let reduce_beq_rat2 = (addrC [0] unfold_rat) thenC (addrC [1] unfold_rat) thenC reduce_beq_rat

define unfold_ge_bool_rat : ge_bool_rat{'a;'b} <--> le_bool_rat{'b;'a}

define unfold_ge_rat : ge_rat{'a;'b} <--> "assert"{ge_bool_rat{'a;'b}}

let reduce_le_bool_rat2 = reduce_le_bool_rat thenC (addrC [0] reduce_mul) thenC (addrC [1] reduce_mul) thenC unfold_le_bool
let reduce_ge_bool_rat = unfold_ge_bool_rat thenC reduce_le_bool_rat2
let reduce_ge_rat = unfold_ge_rat thenC (addrC [0] unfold_ge_bool_rat)

let resource reduce += [
   << add_rat{('a,'b); 'x} >>, addrC [0] fold_rat;
   << add_rat{'x; ('a,'b)} >>, addrC [1] fold_rat;
   << mul_rat{('a,'b); 'x} >>, addrC [0] fold_rat;
   << mul_rat{'x; ('a,'b)} >>, addrC [1] fold_rat;
   << lt_bool_rat{('a,'b); 'x} >>, addrC [0] fold_rat;
   << lt_bool_rat{'x; ('a,'b)} >>, addrC [1] fold_rat;
   << add_rat{rat{'a;'b}; rat{'c;'d}} >>, reduce_add_rat;
   << mul_rat{rat{'a;'b}; rat{'c;'d}} >>, reduce_mul_rat;
   << neg_rat{rat{'a;'b}} >>, reduce_neg_rat;
   << neg_rat{('a,'b)} >>, (addrC [0] fold_rat thenC reduce_neg_rat);
   << lt_bool_rat{rat{'a;'b}; rat{'c;'d}} >>, reduce_lt_bool_rat;
   << beq_rat{('a,'b); ('c,'d)} >>, reduce_beq_rat;
   << beq_rat{rat{'a;'b}; rat{'c;'d}} >>, reduce_beq_rat2;

	<<"assert"{le_bool_rat{rat{number[i:n]; number[j:n]}; rat{number[k:n]; number[l:n]}}}>>, addrC [0] reduce_le_bool_rat2;
	<<"assert"{ge_bool_rat{rat{number[i:n]; number[j:n]}; rat{number[k:n]; number[l:n]}}}>>, addrC [0] reduce_ge_bool_rat;
	<<ge_rat{rat{number[i:n]; number[j:n]}; rat{number[k:n]; number[l:n]}}>>, reduce_ge_rat;
]

let resource elim += [
	<<"assert"{le_bool_rat{rat{number[i:n]; number[j:n]}; rat{number[k:n]; number[l:n]}}}>>, rw (addrC [0] reduce_le_bool_rat2);
	<<"assert"{ge_bool_rat{rat{number[i:n]; number[j:n]}; rat{number[k:n]; number[l:n]}}}>>, rw (addrC [0] reduce_ge_bool_rat);
	<<ge_rat{rat{number[i:n]; number[j:n]}; rat{number[k:n]; number[l:n]}}>>, rw reduce_ge_rat;
	]

let resource intro += [
	<<"assert"{le_bool_rat{rat{number[i:n]; number[j:n]}; rat{number[k:n]; number[l:n]}}}>>, wrap_intro (rw (addrC [0] reduce_le_bool_rat2) 0);
	<<"assert"{ge_bool_rat{rat{number[i:n]; number[j:n]}; rat{number[k:n]; number[l:n]}}}>>, wrap_intro (rw (addrC [0] reduce_ge_bool_rat) 0);
	<<ge_rat{rat{number[i:n]; number[j:n]}; rat{number[k:n]; number[l:n]}}>>, wrap_intro (rw reduce_ge_rat 0);
	]

define unfold_rationals : rationals <-->
	quot x,y: (int * posnat) // "assert"{beq_rat{'x;'y}}

define unfold_fieldQ : fieldQ <-->
	{car=rationals; "*"=lambda{x.lambda{y.mul_rat{'x;'y}}}; "1"=rat{1;1};
	 "+"=lambda{x.lambda{y.add_rat{'x;'y}}}; "0"=rat{0;1}; "neg"=lambda{x.(neg_rat{'x})};
	 car0={a: rationals | 'a <> rat{0;1} in rationals};
	 inv=lambda{x.rat{snd{'x};fst{'x}}}
	}

define unfold_max_rat : max_rat{'a;'b} <-->
	(max{lambda{x.lambda{y.le_bool_rat{'x;'y}}}} 'a 'b)

define unfold_min_rat : min_rat{'a;'b} <-->
	(min{lambda{x.lambda{y.le_bool_rat{'x;'y}}}} 'a 'b)

let fold_rationals = makeFoldC <<rationals>> unfold_rationals

let fold_fieldQ = makeFoldC <<fieldQ>> unfold_fieldQ

doc <:doc< @docoff >>

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)
dform rat_df1 : except_mode[src] :: rat{'a; 'b}
 =
   `"(" slot{'a} `"/" slot{'b} `")"

dform zero_rat_df1 : except_mode[src] :: rat{0;'a}
 =
   `"0" Nuprl_font!subq

dform unit_rat_df1 : except_mode[src] :: rat{'a;'a}
 =
   `"1" Nuprl_font!subq

dform int_rat_df1 : except_mode[src] :: rat{'a;1}
 =
   slot{'a} Nuprl_font!subq

dform add_rat_df1 : except_mode[src] :: parens :: "prec"[prec_add] :: add_rat{'a; 'b}
 =
   slot["le"]{'a} `" +" Nuprl_font!subq `" " slot["lt"]{'b}

dform mul_rat_df1 : except_mode[src] :: parens :: "prec"[prec_add] :: mul_rat{'a; 'b}
 =
   slot["le"]{'a} `" *" Nuprl_font!subq `" " slot["lt"]{'b}

dform ge_rat_df1 : parens :: "prec"[prec_compare] :: ge_rat{'a; 'b} =
   slot["lt"]{'a} `" >=" Nuprl_font!subq `" " slot["le"]{'b}

dform rationals_prl_df : except_mode [src] :: rationals = `"rationals"

(*
dform q_prl_df : except_mode [src] :: Q = mathbbQ
dform q_src_df : mode[src] :: Q = `"Q"
*)

let rationals_term = << rationals >>
let rationals_opname = opname_of_term rationals_term
let is_rationals_term = is_no_subterms_term rationals_opname

let rat_term = << rat{'x;'y} >>
let rat_opname = opname_of_term rat_term
let is_rat_term = is_dep0_dep0_term rat_opname
let mk_rat_term = mk_dep0_dep0_term rat_opname
let dest_rat = dest_dep0_dep0_term rat_opname

let beq_rat_term = << beq_rat{'x; 'y} >>
let beq_rat_opname = opname_of_term beq_rat_term
let is_beq_rat_term = is_dep0_dep0_term beq_rat_opname
let mk_beq_rat_term = mk_dep0_dep0_term beq_rat_opname
let dest_beq_rat = dest_dep0_dep0_term beq_rat_opname

let mul_rat_term = << mul_rat{'x; 'y} >>
let mul_rat_opname = opname_of_term mul_rat_term
let is_mul_rat_term = is_dep0_dep0_term mul_rat_opname
let mk_mul_rat_term = mk_dep0_dep0_term mul_rat_opname
let dest_mul_rat = dest_dep0_dep0_term mul_rat_opname

let add_rat_term = << add_rat{'x; 'y} >>
let add_rat_opname = opname_of_term add_rat_term
let is_add_rat_term = is_dep0_dep0_term add_rat_opname
let mk_add_rat_term = mk_dep0_dep0_term add_rat_opname
let dest_add_rat = dest_dep0_dep0_term add_rat_opname

let neg_rat_term = << neg_rat{'x} >>
let neg_rat_opname = opname_of_term neg_rat_term
let is_neg_rat_term = is_dep0_term neg_rat_opname
let mk_neg_rat_term = mk_dep0_term neg_rat_opname
let dest_neg_rat = dest_dep0_term neg_rat_opname

let inv_rat_term = << inv_rat{'x} >>
let inv_rat_opname = opname_of_term inv_rat_term
let is_inv_rat_term = is_dep0_term inv_rat_opname
let mk_inv_rat_term = mk_dep0_term inv_rat_opname
let dest_inv_rat = dest_dep0_term inv_rat_opname

let le_bool_rat_term = << le_bool_rat{'x; 'y} >>
let le_bool_rat_opname = opname_of_term le_bool_rat_term
let is_le_bool_rat_term = is_dep0_dep0_term le_bool_rat_opname
let mk_le_bool_rat_term = mk_dep0_dep0_term le_bool_rat_opname
let dest_le_bool_rat = dest_dep0_dep0_term le_bool_rat_opname

let ge_bool_rat_term = << ge_bool_rat{'x; 'y} >>
let ge_bool_rat_opname = opname_of_term ge_bool_rat_term
let is_ge_bool_rat_term = is_dep0_dep0_term ge_bool_rat_opname
let mk_ge_bool_rat_term = mk_dep0_dep0_term ge_bool_rat_opname
let dest_ge_bool_rat = dest_dep0_dep0_term ge_bool_rat_opname

let ge_rat_term = << ge_rat{'x; 'y} >>
let ge_rat_opname = opname_of_term ge_rat_term
let is_ge_rat_term = is_dep0_dep0_term ge_rat_opname
let mk_ge_rat_term = mk_dep0_dep0_term ge_rat_opname
let dest_ge_rat = dest_dep0_dep0_term ge_rat_opname

let max_rat_term = << max_rat{'x; 'y} >>
let max_rat_opname = opname_of_term max_rat_term
let is_max_rat_term = is_dep0_dep0_term max_rat_opname
let mk_max_rat_term = mk_dep0_dep0_term max_rat_opname
let dest_max_rat = dest_dep0_dep0_term max_rat_opname

let min_rat_term = << min_rat{'x; 'y} >>
let min_rat_opname = opname_of_term min_rat_term
let is_min_rat_term = is_dep0_dep0_term min_rat_opname
let mk_min_rat_term = mk_dep0_dep0_term min_rat_opname
let dest_min_rat = dest_dep0_dep0_term min_rat_opname

let posnatDT n = rw unfold_posnat n thenT dT n thenT dT (n+1)

(*
let rationalsDT n = rw unfold_rationals n thenT
                    ((dT n) orelseT tryT (squashT thenT dT n thenLT
						                      [idT; (dT n thenT dT (n+1))]))
*)
let rationalsDT n = rw unfold_rationals n thenT dT n

let resource elim += [
	<<posnat>>, posnatDT;
	<<rationals>>, rationalsDT;
	]

interactive rationalsElimination1Eq{| elim [ThinOption thinT] |} 'H :
   [wf] sequent { <H>; a: rationals; <J['a]> >- "type"{'T['a]} } -->
   [main] sequent { <H>; a: quot x,y: (int * posnat) // "assert"{beq_rat{'x;'y}}; <J['a]>;
             u1: int; v1: int; w1:'v1>0;
				 u2: int; v2: int; w2:'v2>0;
				 z: 'u1 *@ 'v2 = 'u2 *@ 'v1 in int >- 's[rat{'u1;'v1}] = 't[rat{'u2;'v2}] in 'T[rat{'u1;'v1}]
           } -->
   sequent { <H>; a: rationals; <J['a]> >- 's['a] = 't['a] in 'T['a] }

interactive rationalsElimination {| elim [ThinOption thinT] |} 'H :
   [wf] sequent { <H>; a: rationals; <J['a]> >- "type"{'C['a]} } -->
   [main] sequent { <H>; a: quot x,y: (int * posnat) // "assert"{beq_rat{'x;'y}}; x: int; y: int; 'y>0; <J['a]> >- squash{'C[rat{'x;'y}]} } -->
   sequent { <H>; a: rationals; <J['a]> >- squash{'C['a]} }

let resource intro += [
	<<'x='y in rationals>>, wrap_intro (rwh unfold_rationals 0);
	]

interactive posnatEquality {| intro [] |} :
	sequent { <H> >- 'a = 'b in int } -->
	sequent { <H> >- 'a > 0 } -->
	sequent { <H> >- 'a = 'b in posnat }

interactive rationals_wf {| intro [] |} :
	sequent { <H> >- rationals Type }

interactive lt_bool_rat_wf1 {| intro [] |} :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in int } -->
	sequent { <H> >- 'd in int } -->
	sequent { <H> >- lt_bool_rat{rat{'a;'b}; rat{'c;'d}} in bool }

interactive lt_bool_rat_wf2 {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in int } -->
	sequent { <H> >- lt_bool_rat{'a; rat{'b;'c}} in bool }

interactive lt_bool_rat_wf3 {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- lt_bool_rat{rat{'a;'b}; 'c} in bool }

interactive lt_bool_rat_wf {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- lt_bool_rat{'a; 'b} in bool }

interactive le_bool_rat_wf1 {| intro [] |} :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in int } -->
	sequent { <H> >- 'd in int } -->
	sequent { <H> >- le_bool_rat{rat{'a;'b}; rat{'c;'d}} in bool }

interactive le_bool_rat_wf2 {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in int } -->
	sequent { <H> >- le_bool_rat{'a; rat{'b;'c}} in bool }

interactive le_bool_rat_wf3 {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- le_bool_rat{rat{'a;'b}; 'c} in bool }

interactive le_bool_rat_wf {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- le_bool_rat{'a; 'b} in bool }

interactive beq_rat_wf1 {| intro [] |} :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in int } -->
	sequent { <H> >- 'd in int } -->
	sequent { <H> >- beq_rat{rat{'a;'b}; rat{'c;'d}} in bool }

interactive beq_rat_wf2 {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in int } -->
	sequent { <H> >- beq_rat{'a; rat{'b;'c}} in bool }

interactive beq_rat_wf3 {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- beq_rat{rat{'a;'b}; 'c} in bool }

interactive beq_rat_wf {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- beq_rat{'a; 'b} in bool }

interactive mul_rat_wf {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- mul_rat{'a;'b} in rationals }

interactive add_rat_wf {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- add_rat{'a;'b} in rationals }

interactive min_rat_wf {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- min_rat{'a;'b} in rationals }

interactive max_rat_wf {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- max_rat{'a;'b} in rationals }

interactive max_self1 {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- ge_rat{max_rat{'a;'b};'a} }

interactive max_self2 {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- ge_rat{max_rat{'a;'b};'b} }

interactive min_self1 {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- ge_rat{'a;min_rat{'a;'b}} }

interactive min_self2 {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- ge_rat{'b;min_rat{'a;'b}} }

interactive ratEquality {| intro [AutoMustComplete] |} :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- "assert"{beq_rat{'a;'b}} } -->
	sequent { <H> >- 'a = 'b in rationals }

interactive ratMembership {| intro [] |} :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in posnat } -->
	sequent { <H> >- rat{'a;'b} in rationals }

interactive rat_of_intEquality {| intro [] |} :
	sequent { <H> >- 'a = 'b in int } -->
	sequent { <H> >- rat_of_int{'a}=rat_of_int{'b} in rationals }

interactive rat_of_intEquality2 :
	sequent { <H> >- rat_of_int{'a}=rat_of_int{'b} in rationals } -->
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'a = 'b in int }

interactive rat_of_intLess {| intro [] |} :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'a < 'b } -->
	sequent { <H> >- "assert"{lt_bool_rat{rat_of_int{'a}; rat_of_int{'b}}} }

interactive rat_of_intLess2 :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	sequent { <H> >- "assert"{lt_bool_rat{rat_of_int{'a}; rat_of_int{'b}}} } -->
	sequent { <H> >- 'a < 'b }

interactive rat_of_intLE {| intro [] |} :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'a <= 'b } -->
	sequent { <H> >- "assert"{le_bool_rat{rat_of_int{'a}; rat_of_int{'b}}} }

interactive rat_of_intLE2 :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	sequent { <H> >- "assert"{le_bool_rat{rat_of_int{'a}; rat_of_int{'b}}} } -->
	sequent { <H> >- 'a <= 'b }

interactive lt_le_rat :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- strict2unstrict{lt_bool_rat{'a;'b}} = le_bool_rat{'a;'b} in bool }

interactive q_is_field {| intro [] |} :
	sequent { <H> >- fieldQ in field[i:l] }

interactive lt_bool_ratStrictTotalOrder :
	sequent { <H> >- isStrictTotalOrder{rationals; lambda{x.lambda{y.lt_bool_rat{'x;'y}}}} }

interactive le_bool_ratUnstrictTotalOrder :
	sequent { <H> >- isUnstrictTotalOrder{rationals; lambda{x.lambda{y.le_bool_rat{'x;'y}}}} }

interactive ge_bool_ratUnstrictTotalOrder :
	sequent { <H> >- isUnstrictTotalOrder{rationals; lambda{x.lambda{y.ge_bool_rat{'x;'y}}}} }

interactive geReflexive {| intro [] |} :
	[wf] sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- ge_rat{'a; 'a} }

interactive geTransitive 'b :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- ge_rat{'b; 'c} } -->
	sequent { <H> >- ge_rat{'a; 'b} } -->
	sequent { <H> >- ge_rat{'a; 'c} }

interactive ge_minLeftIntro :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- ge_rat{'a; 'c} } -->
	sequent { <H> >- ge_rat{'b; 'c} } -->
	sequent { <H> >- ge_rat{min_rat{'a;'b}; 'c} }

interactive ge_maxRightIntro :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- ge_rat{'a; 'b} } -->
	sequent { <H> >- ge_rat{'a; 'c} } -->
	sequent { <H> >- ge_rat{'a;max_rat{'b;'c}} }

interactive ge_minLeftElim {| elim [] |} 'H :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	sequent { <H>; ge_rat{'a; 'c}; ge_rat{'b; 'c}; <J> >- 'C } -->
	sequent { <H>; ge_rat{min_rat{'a;'b}; 'c}; <J> >- 'C }

interactive ge_maxRightElim {| elim [] |} 'H :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	sequent { <H>; ge_rat{'a;'b}; ge_rat{'a;'c}; <J> >- 'C } -->
	sequent { <H>; ge_rat{'a;max_rat{'b;'c}}; <J> >- 'C }

interactive max_ge_maxIntro :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	[wf] sequent { <H> >- 'd in rationals } -->
	sequent { <H> >- ge_rat{'a;'b} } -->
	sequent { <H> >- ge_rat{'c;'d} } -->
	sequent { <H> >- ge_rat{max_rat{'a;'c};max_rat{'b;'d}} }

interactive min_ge_minIntro :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	[wf] sequent { <H> >- 'd in rationals } -->
	sequent { <H> >- ge_rat{'a;'b} } -->
	sequent { <H> >- ge_rat{'c;'d} } -->
	sequent { <H> >- ge_rat{min_rat{'a;'c};min_rat{'b;'d}} }

interactive max_ge_minIntro {| intro [] |} :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- ge_rat{max_rat{'a;'b};min_rat{'a;'b}} }

interactive ge_addMono 'c :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- ge_rat{add_rat{'a;'c};add_rat{'b;'c}} } -->
	sequent { <H> >- ge_rat{'a;'b} }

interactive ge_addMonoElim 'H 'c :
	[wf] sequent { <H>; w: ge_rat{'a;'b}; <J['w]> >- 'a in rationals } -->
	[wf] sequent { <H>; w: ge_rat{'a;'b}; <J['w]> >- 'b in rationals } -->
	[wf] sequent { <H>; w: ge_rat{'a;'b}; <J['w]> >- 'c in rationals } -->
	sequent { <H>; w: ge_rat{'a;'b}; <J['w]>; ge_rat{add_rat{'a;'c};add_rat{'b;'c}} >- 'C['w] } -->
	sequent { <H>; w: ge_rat{'a;'b}; <J['w]> >- 'C['w] }

doc <:doc< @docoff >>
