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
extends Itt_int_arith
doc <:doc< @docoff >>

open Lm_debug
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Top_conversionals

open Base_meta
open Auto_tactic
open Dtactic

open Itt_equal
open Itt_struct
open Itt_squash
open Itt_bool
open Itt_squiggle

open Itt_int_base
open Itt_int_ext
open Itt_int_arith

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

declare rationals
declare rat{'a;'b}
declare beq_rat{'a;'b}

define unfold_rat_of_int :
   rat_of_int{'a} <--> rat{'a ; 1}

doc <:doc<
   @begin[doc]
   The basic arithmetic operators are defined with
   the following terms. Basic predicates are boolean.
   @end[doc]
>>

rewrite reduce_add_rat : (rat{'a;'b} +@ rat{'c;'d}) <--> rat{(('a *@ 'd) +@ ('c *@ 'b)); ('b *@ 'd)}
rewrite reduce_mul_rat : (rat{'a;'b} *@ rat{'c;'d}) <--> rat{('a *@ 'c); ('b *@ 'd)}
rewrite reduce_minus_rat : minus{rat{'a;'b}} <--> rat{minus{'a};'b}
rewrite reduce_lt_bool_rat : lt_bool{rat{'a;'b};rat{'c;'d}} <--> lt_bool{('a *@ 'd);('c *@ 'b)}

rewrite unfold_beq_rat :
   beq_rat{ rat{ 'a ; 'b } ; rat{ 'c ; 'd } } <--> beq_int{ ('a *@ 'd) ; ('c *@ 'b) }

doc <:doc< @docoff >>

val rationals_term : term
val is_rationals_term : term -> bool

val beq_rat_term : term
val is_beq_rat_term : term -> bool
val mk_beq_rat_term : term -> term -> term
val dest_beq_rat : term -> term * term

val rat_term : term
val is_rat_term : term -> bool
val mk_rat_term : term -> term -> term
val dest_rat : term -> term * term

doc <:doc<
   @begin[doc]
   @modsubsection{Typehood and well-formedness of @tt[rationals] and @tt[rat]}

   The $@rationals$ type inhabits every universe, and it
   is a type.
   @end[doc]
>>

rule rationalsEquality :
   sequent { <H> >- rationals in univ[i:l] }

(*
 * H >- rationals Type
 *)
rule rationalsType :
   sequent { <H> >- "type"{rationals} }

(*
 * H >- Ui ext Q
 * by rationalsFormation
 *)
rule rationalsFormation :
   sequent { <H> >- univ[i:l] }

(*
 * H >- Q ext rat{}
 * by ratFormation rat{'a;'b}
 *)
rule ratFormation number[n:n] number[m:n]:
   sequent { <H> >- number[m:n] > 0 } -->
   sequent { <H> >- rationals }

doc <:doc<
   @begin[doc]
   @modsubsection{Well-formedness of operations and relations}

   @end[doc]
>>

rule add_rat_wf :
   [wf] sequent { <H> >- 'a = 'a1 in rationals } -->
   [wf] sequent { <H> >- 'b = 'b1 in rationals } -->
   sequent { <H> >- 'a +@ 'b = 'a1 +@ 'b1 in rationals }

rule minus_rat_wf :
   [wf] sequent { <H> >- 'a = 'a1 in rationals } -->
   sequent { <H> >- (-'a) = (-'a1) in rationals }

rule sub_rat_wf :
   [wf] sequent { <H> >- 'a = 'a1 in rationals } -->
   [wf] sequent { <H> >- 'b = 'b1 in rationals } -->
   sequent { <H> >- 'a -@ 'b = 'a1 -@ 'b1 in rationals }

rule lt_bool_rat_wf :
   sequent { <H> >- 'a='a1 in rationals } -->
   sequent { <H> >- 'b='b1 in rationals } -->
   sequent { <H> >- lt_bool{'a; 'b} = lt_bool{'a1; 'b1} in bool }

rule beq_rat_wf :
   [wf] sequent { <H> >- 'a = 'a1 in rationals } -->
   [wf] sequent { <H> >- 'b = 'b1 in rationals } -->
   sequent { <H> >- beq_rat{'a; 'b} = beq_rat{'a1; 'b1} in bool }

rule lt_rat_squashStable :
   sequent { <H> >- 'a < 'b } -->
   sequent { <H> >- it in ('a < 'b) }

rule lt_rat_wf :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   sequent { <H> >- "type"{lt{'a; 'b}} }

doc <:doc<
   @begin[doc]
   @modsubsection{Correspondence between <<beq_rat{'a;'b}>> and <<'a='b in rationals>> }

   @end[doc]
>>
rule beq_rat2prop :
   [main] sequent { <H> >- "assert"{beq_rat{'a; 'b}} } -->
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   sequent { <H> >- 'a = 'b in rationals }

(* Derived from previous *)
rule eq_rat_assert_elim 'H :
   [main]sequent{ <H>; x:"assert"{beq_rat{'a;'b}}; <J[it]>;
                            y: 'a = 'b in rationals >- 'C[it]} -->
   [wf]sequent{ <H>; x:"assert"{beq_rat{'a;'b}}; <J[it]> >- 'a in rationals} -->
   [wf]sequent{ <H>; x:"assert"{beq_rat{'a;'b}}; <J[it]> >- 'b in rationals} -->
   sequent{ <H>; x:"assert"{beq_rat{'a;'b}}; <J['x]> >- 'C['x]}

rewrite beq_rat_is_true_rw :
   ('a = 'b in rationals) -->
   beq_rat{'a; 'b} <--> btrue

topval beq_rat_is_trueC : conv

(*
 Derived from previous rewrite
 *)
rule eq_2beq_rat :
   sequent { <H> >- 'a = 'b in rationals } -->
   sequent { <H> >- "assert"{beq_rat{'a; 'b}} }

rule lt_bool_rat_member :
  [main]  sequent { <H> >- 'a < 'b } -->
(*  [wf] sequent { <H> >- 'a in rationals } -->
  [wf] sequent { <H> >- 'b in rationals } --> *)
  sequent { <H> >- "assert"{lt_bool{'a; 'b}} }

doc <:doc<
   @begin[doc]
   @modsubsection{Decidability}
   The following rules establish decidability of rationalseger relations and
   improve the @hreftactic[decideT] tactic.
   @end[doc]
>>
rule lt_rat_decidable :
   [wf] sequent{ <H> >- 'a in rationals } -->
   [wf] sequent{ <H> >- 'b in rationals } -->
   sequent{ <H> >- decidable{('a < 'b)} }

rule eq_rat_decidable :
   [wf] sequent{ <H> >- 'a in rationals } -->
   [wf] sequent{ <H> >- 'b in rationals } -->
   sequent{ <H> >- decidable{('a = 'b in rationals)} }

doc <:doc<
   @begin[doc]
   @modsubsection{Membership}

   The $@rationals$ type contains the @hrefterm[number] terms.
   @end[doc]
>>
(*
 * H >- rat{'a;'b} = rat{'a;'b} in rationals
 * by numberEquality
 *)
rule ratEquality :
   [wf] sequent{ <H> >- 'a in int } -->
   [wf] sequent{ <H> >- 'b in posnat } -->
   sequent { <H> >- rat{'a;'b} in rationals }

doc <:doc<
   @begin[doc]
   @modsubsection{Order relation properties}

   <<lt_bool{'a;'b}>> defines irreflexive, asymmetric, transitive and
   discrete order on @tt[rationals]
   @end[doc]
>>

rule lt_rat_Reflex :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   sequent { <H> >- band{lt_bool{'a; 'b}; lt_bool{'b; 'a}} ~ bfalse }

rewrite lt_rat_Reflex_rw :
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   band{lt_bool{'a; 'b}; lt_bool{'b; 'a}} <--> bfalse

topval lt_rat_ReflexC : conv

rewrite lt_rat_irreflex_rw :
   ( 'a in rationals ) -->
   lt_bool{'a;'a} <--> bfalse

topval lt_rat_IrreflexC : conv

rule lt_rat_Asym 'a 'b :
   [main] sequent { <H> >- 'a < 'b } -->
   [main] sequent { <H> >- 'b < 'a } -->
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   sequent { <H> >- 'C }

topval lt_rat_AsymT : term -> term -> tactic

rule lt_rat_Trichot :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   sequent {
     <H> >- bor{bor{lt_bool{'a; 'b};lt_bool{'b; 'a}}; beq_int{'a; 'b}} ~ btrue
 }

rewrite lt_rat_Trichot_rw :
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   bor{bor{lt_bool{'a; 'b};lt_bool{'b; 'a}}; beq_int{'a; 'b}} <--> btrue

topval lt_rat_TrichotC : conv

topval splitRationalsC : term -> term -> conv

rule splitRationals 'a 'b :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   [main] sequent { <H>; w: ('a < 'b) >- 'C } -->
   [main] sequent { <H>; w: 'a = 'b in rationals >- 'C } -->
   [main] sequent { <H>; w: ('b < 'a) >- 'C } -->
   sequent { <H> >- 'C }

doc <:doc<
   @begin[description]
   @item{@tactic[splitrationalsT];
    { The @tt[splitrationalsT] <<'a>> <<'b>> tactic uses @tt[splitrationals] rule to split
      reasoning rationalso three cases - when <<'a>> is less then, equal to or
      greater then <<'b>>.}}
   @end[description]
>>

topval splitRationalsT : term -> term -> tactic

rule lt_rat_Transit 'b :
   [main] sequent {
      <H> >- band{lt_bool{'a; 'b};lt_bool{'b; 'c}} = btrue in bool } -->
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   [wf] sequent { <H> >- 'c in rationals } -->
   sequent { <H> >- lt_bool{'a; 'c} ~ btrue }

rewrite lt_rat_Transit_rw 'b :
   ( band{lt_bool{'a; 'b};lt_bool{'b; 'c}} = btrue in bool ) -->
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   ( 'c in rationals ) -->
   lt_bool{'a; 'c} <--> btrue

topval lt_rat_TransitC : term -> conv

doc <:doc<
   @begin[doc]
   @modsubsection{Addition properties}

   @tt[add] is commutative and associative.

   @end[doc]
>>
rule add_rat_Commut :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   sequent { <H> >- ('a +@ 'b) ~ ('b +@ 'a) }

rewrite add_rat_Commut_rw :
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   ('a +@ 'b) <--> ('b +@ 'a)

topval add_rat_CommutC : conv

rule add_rat_Assoc :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   [wf] sequent { <H> >- 'c in rationals } -->
   sequent { <H> >- ('a +@ ('b +@ 'c)) ~ (('a +@ 'b) +@ 'c) }

rewrite add_rat_Assoc_rw :
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   ( 'c in rationals ) -->
   ('a +@ ('b +@ 'c)) <--> (('a +@ 'b) +@ 'c)

topval add_rat_AssocC : conv

rewrite add_rat_Assoc2_rw :
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   ( 'c in rationals ) -->
   (('a +@ 'b) +@ 'c) <--> ('a +@ ('b +@ 'c))

topval add_rat_Assoc2C : conv

doc <:doc<
   @begin[doc]

   0 is neutral element for @tt[add] in @tt[rationals]

   @end[doc]
>>
rule add_rat_Id :
   [wf] sequent { <H> >- 'a in rationals } -->
   sequent { <H> >- ('a +@ 0) ~ 'a }

rewrite add_rat_Id_rw :
   ( 'a in rationals ) -->
   ('a +@ 0) <--> 'a

topval add_rat_IdC : conv

rewrite add_rat_Id2_rw :
   ( 'a in rationals ) -->
   (0 +@ 'a) <--> 'a

topval add_rat_Id2C : conv

rewrite add_rat_Id3_rw :
   ( 'a in rationals ) -->
   'a <--> (0 +@ 'a)

topval add_rat_Id3C : conv

rewrite add_rat_Id4_rw :
   ( 'a in rationals ) -->
   'a <--> ('a +@ 0)

topval add_rat_Id4C : conv

doc <:doc<
   @begin[doc]

   Monotonicity:

   @end[doc]
>>
rule lt_rat_addMono 'c :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   [wf] sequent { <H> >- 'c in rationals } -->
   sequent { <H> >- lt_bool{'a; 'b} ~ lt_bool{('a +@ 'c); ('b +@ 'c)} }

rewrite lt_rat_addMono_rw 'c :
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   ( 'c in rationals ) -->
   lt_bool{'a; 'b} <--> lt_bool{('a +@ 'c); ('b +@ 'c)}

topval lt_rat_addMonoC : term -> conv

rule lt_rat_add_lt :
   [main] sequent { <H> >- 'a < 'b} -->
   [main] sequent { <H> >- 'c < 'd} -->
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   [wf] sequent { <H> >- 'c in rationals } -->
   [wf] sequent { <H> >- 'd in rationals } -->
   sequent { <H> >- ('a +@ 'c) < ('b +@ 'd) }

topval lt_rat_add_ltT : tactic

doc <:doc<
   @begin[doc]

   <<- 'a>> is an inverse element for <<'a>> in <<rationals>>

   @end[doc]
>>
rule minus_rat_add_inverse :
   [wf] sequent { <H> >- 'a in rationals } -->
   sequent { <H> >- ( 'a +@ (- 'a ) ) ~ 0 }

rewrite minus_rat_add_inverse_rw :
   ( 'a in rationals ) -->
   ( 'a +@ (- 'a) ) <--> 0

topval minus_rat_add_inverseC : conv

rule add_rat_Functionality 'c :
   [main] sequent { <H> >- ('a +@ 'c) ~ ('b +@ 'c) } -->
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   [wf] sequent { <H> >- 'c in rationals } -->
   sequent { <H> >- 'a ~ 'b }

rewrite add_rat_Functionality_rw 'b 'c :
   (('a +@ 'c) ~ ('b +@ 'c)) -->
   ('a in rationals) -->
   ('b in rationals) -->
   ('c in rationals) -->
   'a <--> 'b

topval add_rat_FunctionalityC : term -> term -> conv

rule minus_add_rat_Distrib :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   sequent { <H> >- (-('a +@ 'b)) ~ ((-'a) +@ (-'b)) }

rule minus_minus_rat_reduce :
   [wf] sequent { <H> >- 'a in rationals } -->
   sequent { <H> >- (-(-'a)) ~ 'a }

rewrite minus_minus_rat_reduce_rw :
   ('a in rationals) -->
   (-(-'a)) <--> 'a

topval minus_minus_rat_reduceC : conv

rewrite minus_same_rat_rw :
   ('a in rationals) -->
   ('a -@ 'a) <--> 0

rewrite plus_minus_rat_rw :
   ('a in rationals) -->
   ('b in rationals) -->
   (('a +@ 'b) -@ 'b) <--> 'a

rewrite minus_plus_rat_rw :
   ('a in rationals) -->
   ('b in rationals) -->
   (('a -@ 'b) +@ 'b) <--> 'a

doc <:doc< @docoff >>