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

let _ = show_loading "Loading Itt_rat%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @terms

   The @tt[int] term is the type of integers with elements
   $$@ldots, @number{-2}, @number{-1}, @number{0}, @number{1}, @number{2},
 @ldots$$
   @end[doc]
>>

define unfold_posnat :
   posnat <--> ({x:int | 'x>0})

define unfold_int0 :
   int0 <--> ({x:int | 'x<>0})

declare add_rat{'a;'b}
declare mul_rat{'a;'b}
declare neg_rat{'a}
declare lt_bool_rat{'a;'b}
declare beq_rat{'a;'b}

define unfold_rat_of_int :
   rat_of_int{'a} <--> ('a, 1)

doc <:doc<
   @begin[doc]
   The basic arithmetic operators are defined with
   the following terms. Basic predicates are boolean.
   @end[doc]
>>

prim_rw reduce_add_rat : add_rat{('a,'b); ('c,'d)} <--> ((('a *@ 'd) +@ ('c *@ 'b)), ('b *@ 'd))
prim_rw reduce_mul_rat : mul_rat{('a,'b); ('c,'d)} <--> (('a *@ 'c), ('b *@ 'd))
prim_rw reduce_neg_rat : neg_rat{('a,'b)} <--> (minus{'a},'b)
prim_rw reduce_lt_bool_rat : lt_bool_rat{('a,'b);('c,'d)} <--> lt_bool{('a *@ 'd);('c *@ 'b)}

prim_rw reduce_beq_rat :
   beq_rat{ ('a,'b) ; ('c,'d) } <--> beq_int{ ('a *@ 'd) ; ('c *@ 'b) }

let resource reduce += [
   << add_rat{('a,'b); ('c,'d)} >>, reduce_add_rat;
   << mul_rat{('a,'b); ('c,'d)} >>, reduce_mul_rat;
   << neg_rat{('a,'b)} >>, reduce_neg_rat;
   << lt_bool_rat{('a,'b); ('c,'d)} >>, reduce_lt_bool_rat;
   << beq_rat{('a,'b); ('c,'d)} >>, reduce_beq_rat;
]

define unfold_rationals : rationals <-->
	quot x,y: (int * posnat) // "assert"{beq_rat{'x;'y}}

define unfold_fieldQ : fieldQ <-->
	{car=rationals; "*"=lambda{x.lambda{y.mul_rat{'x;'y}}}; "1"=(1,1);
	 "+"=lambda{x.lambda{y.add_rat{'x;'y}}}; "0"=(0,1); "neg"=lambda{x.(neg_rat{'x})};
	 car0={a: rationals | 'a <> (0,1) in rationals};
	 inv=lambda{x.(snd{'x},fst{'x})}
	}

let fold_rationals = makeFoldC <<rationals>> unfold_rationals

let fold_fieldQ = makeFoldC <<fieldQ>> unfold_fieldQ

doc <:doc< @docoff >>

let rationals_term = << rationals >>
let rationals_opname = opname_of_term rationals_term
let is_rationals_term = is_no_subterms_term rationals_opname

let beq_rat_term = << beq_rat{'x; 'y} >>
let beq_rat_opname = opname_of_term beq_rat_term
let is_beq_rat_term = is_dep0_dep0_term beq_rat_opname
let mk_beq_rat_term = mk_dep0_dep0_term beq_rat_opname
let dest_beq_rat = dest_dep0_dep0_term beq_rat_opname

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
				 z: 'u1 *@ 'v2 = 'u2 *@ 'v1 in int >- 's[('u1,'v1)] = 't[('u2,'v2)] in 'T[('u1,'v1)]
           } -->
   sequent { <H>; a: rationals; <J['a]> >- 's['a] = 't['a] in 'T['a] }

interactive rationalsElimination {| elim [ThinOption thinT] |} 'H :
   [wf] sequent { <H>; a: rationals; <J['a]> >- "type"{'C['a]} } -->
   [main] sequent { <H>; a: quot x,y: (int * posnat) // "assert"{beq_rat{'x;'y}}; x: int; y: int; 'y>0; <J['a]> >- squash{'C[('x,'y)]} } -->
   sequent { <H>; a: rationals; <J['a]> >- squash{'C['a]} }

let resource intro += [
	<<'x='y in rationals>>, wrap_intro (rwh unfold_rationals 0);
	]

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)
(*
dform q_prl_df : except_mode [src] :: Q = mathbbQ
dform q_src_df : mode[src] :: Q = `"Q"
*)

interactive rationals_wf {| intro [] |} :
	sequent { <H> >- rationals Type }

interactive lt_bool_rat_wf1 {| intro [] |} :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in int } -->
	sequent { <H> >- 'd in int } -->
	sequent { <H> >- lt_bool_rat{('a,'b); ('c,'d)} in bool }

interactive lt_bool_rat_wf2 {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in int } -->
	sequent { <H> >- lt_bool_rat{'a; ('b,'c)} in bool }

interactive lt_bool_rat_wf3 {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- lt_bool_rat{('a,'b); 'c} in bool }

interactive lt_bool_rat_wf {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- lt_bool_rat{'a; 'b} in bool }

(*
interactive lt_bool_rat_wf2 {| intro [] |} :
	sequent { <H> >- 'a in quot x,y: (int * posnat) // "assert"{beq_rat{'x;'y}} } -->
	sequent { <H> >- 'b in quot x,y: (int * posnat) // "assert"{beq_rat{'x;'y}} } -->
	sequent { <H> >- lt_bool_rat{'a; 'b} in bool }
*)
interactive beq_rat_wf {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- beq_rat{'a; 'b} in bool }
(*
interactive beq_rat_wf2 {| intro [] |} :
	sequent { <H> >- 'a in quot x,y: (int * posnat) // "assert"{beq_rat{'x;'y}} } -->
	sequent { <H> >- 'b in quot x,y: (int * posnat) // "assert"{beq_rat{'x;'y}} } -->
	sequent { <H> >- beq_rat{'a; 'b} in bool }
*)

interactive ratEquality {| intro [AutoMustComplete] |} :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- "assert"{beq_rat{'a;'b}} } -->
	sequent { <H> >- 'a = 'b in rationals }

interactive q_is_field {| intro [] |} :
	sequent { <H> >- fieldQ in field[i:l] }

interactive lt_bool_ratStrictTotalOrder :
	sequent { <H> >- isStrictTotalOrder{rationals; lambda{x.lambda{y.lt_bool_rat{'x;'y}}}} }

doc <:doc< @docoff >>
