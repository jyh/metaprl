(*
 * Rational numbers axiomatization.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Yegor Bryukhov
 * @email{ybryukhov@gc.cuny.edu}
 *)
extends Itt_equal
extends Itt_bool
extends Itt_logic
extends Itt_struct
extends Itt_decidable
extends Itt_nequal
extends Itt_order
extends Itt_int_arith
extends Itt_labels

open Basic_tactics

define unfold_posnat :
   posnat <--> ({x:int | 'x>0})

define unfold_int0 :
   int0 <--> ({x:int | 'x<>0})

define unfold_let_in : let_in{'e1; v.'e2['v]} <--> 'e2['e1]

declare gcd{'a;'b}

declare ratn{'a; 'b}
topval fold_ratn : conv

declare rat{'a; 'b}
topval unfold_rat : conv

define unfold_rat_of_int : rat_of_int{'a} <--> rat{'a; 1}

declare rationals
topval unfold_rationals : conv
topval fold_rationals : conv

define unfold_mul_rat : mul_rat{'x; 'y} <-->
	spread{'x; x1,x2.spread{'y; y1,y2.rat{'x1 *@ 'y1; 'x2 *@ 'y2}}}

define unfold_add_rat : add_rat{'x; 'y} <-->
	spread{'x; x1,x2.spread{'y; y1,y2.rat{('x1 *@ 'y2) +@ ('x2 *@ 'y1); 'x2 *@ 'y2}}}

define unfold_neg_rat : neg_rat{'x} <-->
	spread{'x; x1,x2.rat{- 'x1; 'x2}}

define unfold_inv_rat : inv_rat{'x} <-->
	spread{'x; x1,x2.rat{'x2; 'x1}}

define unfold_sub_rat : sub_rat{'x; 'y} <-->
	add_rat{'x; neg_rat{'y}}

declare beq_rat{'a;'b}
declare bneq_rat{'a;'b}
declare neq_rat{'a;'b}
declare lt_bool_rat{'a;'b}
declare le_bool_rat{'a;'b}
declare ge_bool_rat{'a;'b}
declare gt_bool_rat{'a;'b}
declare lt_rat{'a;'b}
declare le_rat{'a;'b}
declare ge_rat{'a;'b}
declare gt_rat{'a;'b}

topval reduce_multiplierC : conv
topval inject_multiplierC : term -> conv
topval reduce_add_rat : conv
topval reduce_mul_rat : conv
topval reduce_neg_rat : conv
topval reduce_inv_rat : conv
topval reduce_beq_rat : conv

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

val is_rationals_term : term -> bool
val rationals_term : term

val is_ratn_term : term -> bool
(*val mk_rat_term : term -> term -> term*)
val dest_ratn : term -> (term * term)

val is_rat_term : term -> bool
val mk_rat_term : term -> term -> term
val dest_rat : term -> (term * term)

val is_rat_of_int_term : term -> bool
val mk_rat_of_int_term : term -> term
val dest_rat_of_int : term -> term

val is_add_rat_term : term -> bool
val mk_add_rat_term : term -> term -> term
val dest_add_rat : term -> (term * term)

val is_mul_rat_term : term -> bool
val mk_mul_rat_term : term -> term -> term
val dest_mul_rat : term -> (term * term)

val is_neg_rat_term : term -> bool
val mk_neg_rat_term : term -> term
val dest_neg_rat : term -> term

val is_inv_rat_term : term -> bool
val mk_inv_rat_term : term -> term
val dest_inv_rat : term -> term

val is_le_bool_rat_term : term -> bool
val mk_le_bool_rat_term : term -> term -> term
val dest_le_bool_rat : term -> (term * term)

val is_ge_bool_rat_term : term -> bool
val mk_ge_bool_rat_term : term -> term -> term
val dest_ge_bool_rat : term -> (term * term)

val is_ge_rat_term : term -> bool
val mk_ge_rat_term : term -> term -> term
val dest_ge_rat : term -> (term * term)

val is_max_rat_term : term -> bool
val mk_max_rat_term : term -> term -> term
val dest_max_rat : term -> (term * term)

val is_min_rat_term : term -> bool
val mk_min_rat_term : term -> term -> term
val dest_min_rat : term -> (term * term)

rule rat_wf :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int0 } -->
	sequent { <H> >- rat{'a; 'b} in rationals }

rule ratEquality :
	sequent { <H> >- 'a *@ 'd = 'b *@ 'c in int } -->
	[wf] sequent { <H> >- rat{'a; 'b} in rationals } -->
	[wf] sequent { <H> >- rat{'c; 'd} in rationals } -->
	sequent { <H> >- rat{'a; 'b} ~ rat{'c; 'd} }

rule geReflexive :
	[wf] sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- ge_rat{'a; 'a} }

rule geTransitive 'b :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- ge_rat{'b; 'c} } -->
	sequent { <H> >- ge_rat{'a; 'b} } -->
	sequent { <H> >- ge_rat{'a; 'c} }

rule ge_minLeftIntro :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- ge_rat{'a; 'c} } -->
	sequent { <H> >- ge_rat{'b; 'c} } -->
	sequent { <H> >- ge_rat{min_rat{'a;'b}; 'c} }

rule ge_maxRightIntro :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- ge_rat{'a; 'b} } -->
	sequent { <H> >- ge_rat{'a; 'c} } -->
	sequent { <H> >- ge_rat{'a;max_rat{'b;'c}} }

rule max_ge_maxIntro :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	[wf] sequent { <H> >- 'd in rationals } -->
	sequent { <H> >- ge_rat{'a;'b} } -->
	sequent { <H> >- ge_rat{'c;'d} } -->
	sequent { <H> >- ge_rat{max_rat{'a;'c};max_rat{'b;'d}} }

rule ge_minLeftElim 'H :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	sequent { <H>; ge_rat{'a; 'c}; ge_rat{'b; 'c}; <J> >- 'C } -->
	sequent { <H>; ge_rat{min_rat{'a;'b}; 'c}; <J> >- 'C }

rule ge_maxRightElim 'H :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	sequent { <H>; ge_rat{'a;'b}; ge_rat{'a;'c}; <J> >- 'C } -->
	sequent { <H>; ge_rat{'a;max_rat{'b;'c}}; <J> >- 'C }

rule min_ge_minIntro :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	[wf] sequent { <H> >- 'd in rationals } -->
	sequent { <H> >- ge_rat{'a;'b} } -->
	sequent { <H> >- ge_rat{'c;'d} } -->
	sequent { <H> >- ge_rat{min_rat{'a;'c};min_rat{'b;'d}} }

rule ge_addMono 'c :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- ge_rat{add_rat{'a;'c};add_rat{'b;'c}} } -->
	sequent { <H> >- ge_rat{'a;'b} }

rule ge_addMonoElim 'H 'c :
	[wf] sequent { <H>; w: ge_rat{'a;'b}; <J['w]> >- 'a in rationals } -->
	[wf] sequent { <H>; w: ge_rat{'a;'b}; <J['w]> >- 'b in rationals } -->
	[wf] sequent { <H>; w: ge_rat{'a;'b}; <J['w]> >- 'c in rationals } -->
	sequent { <H>; w: ge_rat{'a;'b}; <J['w]>; ge_rat{add_rat{'a;'c};add_rat{'b;'c}} >- 'C['w] } -->
	sequent { <H>; w: ge_rat{'a;'b}; <J['w]> >- 'C['w] }

topval ratn2ratC : conv
topval add_rat_IdC : conv
topval add_rat_Id2C : conv
topval add_rat_CommutC : conv
topval add_rat_AssocC : conv
topval add_rat_Assoc2C : conv
topval mul_rat_IdC : conv
topval mul_rat_Id2C : conv
topval mul_rat_CommutC : conv
topval mul_rat_AssocC : conv
topval mul_rat_Assoc2C : conv
topval mul_rat_add_DistribC : conv
topval mul_rat_add_Distrib3C : conv
topval rat_of_int_ratnC : conv

topval int2ratTopC : conv
topval int2ratC : conv
topval int2ratT : tactic
