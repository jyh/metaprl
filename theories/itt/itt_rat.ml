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

prim_rw reduce_add_rat : (rat{'a;'b} +@ rat{'c;'d}) <--> rat{(('a *@ 'd) +@ ('c *@ 'b)); ('b *@ 'd)}
prim_rw reduce_mul_rat : (rat{'a;'b} *@ rat{'c;'d}) <--> rat{('a *@ 'c); ('b *@ 'd)}
prim_rw reduce_minus_rat : minus{rat{'a;'b}} <--> rat{minus{'a};'b}
prim_rw reduce_lt_bool_rat : lt_bool{rat{'a;'b};rat{'c;'d}} <--> lt_bool{('a *@ 'd);('c *@ 'b)}

(*define unfold_beq_rat :
   beq_rat{ rat{ 'a ; 'b } ; rat{ 'c ; 'd } } <--> beq_int{ ('a *@ 'd) ; ('c *@ 'b) }
*)
prim_rw unfold_beq_rat :
   beq_rat{ rat{ 'a ; 'b } ; rat{ 'c ; 'd } } <--> beq_int{ ('a *@ 'd) ; ('c *@ 'b) }

doc <:doc< @docoff >>

let rationals_term = << rationals >>
let rationals_opname = opname_of_term rationals_term
let is_rationals_term = is_no_subterms_term rationals_opname

let beq_rat_term = << beq_rat{'x; 'y} >>
let beq_rat_opname = opname_of_term beq_rat_term
let is_beq_rat_term = is_dep0_dep0_term beq_rat_opname
let mk_beq_rat_term = mk_dep0_dep0_term beq_rat_opname
let dest_beq_rat = dest_dep0_dep0_term beq_rat_opname

let rat_term = << rat{ 'a ; 'b } >>
let rat_opname = opname_of_term rat_term
let is_rat_term = is_dep0_dep0_term rat_opname
let mk_rat_term = mk_dep0_dep0_term rat_opname
let dest_rat = dest_dep0_dep0_term rat_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform rationals_prl_df : except_mode [src] :: rationals = mathbbQ
dform rationals_src_df : mode[src] :: rationals = `"rationals"


doc <:doc<
   @begin[doc]
   @modsubsection{Typehood and well-formedness of @tt[rationals] and @tt[rat]}

   The $Q$ type inhabits every universe, and it
   is a type.
   @end[doc]
>>

prim rationalsEquality {| intro []; eqcd |} :
   sequent { <H> >- rationals in univ[i:l] } = it

(*
 * H >- rationals Type
 *)
interactive rationalsType {| intro [] |} :
   sequent { <H> >- "type"{rationals} }

(*
 * H >- Ui ext Q
 * by rationalsFormation
 *)
interactive rationalsFormation :
   sequent { <H> >- univ[i:l] }

(*
 * H >- Q ext rat{}
 * by ratFormation rat{'a;'b}
 *)
prim ratFormation {| intro [] |} number[n:n] number[m:n]:
   sequent { <H> >- number[m:n] > 0 } -->
   sequent { <H> >- rationals } = rat{number[n:n]; number[m:n]}

doc <:doc<
   @begin[doc]
   @modsubsection{Well-formedness of operations and relations}

   @end[doc]
>>

prim add_rat_wf {| intro [complete_unless_member]; eqcd |} :
   [wf] sequent { <H> >- 'a = 'a1 in rationals } -->
   [wf] sequent { <H> >- 'b = 'b1 in rationals } -->
   sequent { <H> >- 'a +@ 'b = 'a1 +@ 'b1 in rationals } = it

prim minus_rat_wf {| intro []; eqcd |} :
   [wf] sequent { <H> >- 'a = 'a1 in rationals } -->
   sequent { <H> >- (-'a) = (-'a1) in rationals } = it

interactive sub_rat_wf {| intro [complete_unless_member]; eqcd |} :
   [wf] sequent { <H> >- 'a = 'a1 in rationals } -->
   [wf] sequent { <H> >- 'b = 'b1 in rationals } -->
   sequent { <H> >- 'a -@ 'b = 'a1 -@ 'b1 in rationals }

prim lt_bool_rat_wf {| intro [complete_unless_member]; eqcd |} :
   sequent { <H> >- 'a='a1 in rationals } -->
   sequent { <H> >- 'b='b1 in rationals } -->
   sequent { <H> >- lt_bool{'a; 'b} = lt_bool{'a1; 'b1} in bool } = it

prim beq_rat_wf {| intro [complete_unless_member]; eqcd |} :
   [wf] sequent { <H> >- 'a = 'a1 in rationals } -->
   [wf] sequent { <H> >- 'b = 'b1 in rationals } -->
   sequent { <H> >- beq_rat{'a; 'b} = beq_rat{'a1; 'b1} in bool } = it

interactive lt_rat_squashStable (*{| squash |}*) :
   sequent { <H> >- 'a < 'b } -->
   sequent { <H> >- it in ('a < 'b) }

interactive lt_rat_wf {| intro [] |} :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   sequent { <H> >- "type"{lt{'a; 'b}} }

doc <:doc<
   @begin[doc]
   @modsubsection{Correspondence between <<beq_rat{'a;'b}>> and <<'a='b in rationals>> }

   @end[doc]
>>
prim beq_rat2prop :
   [main] sequent { <H> >- "assert"{beq_rat{'a; 'b}} } -->
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   sequent { <H> >- 'a = 'b in rationals } = it

(* Derived from previous *)
interactive eq_rat_assert_elim {| elim [ThinOption thinT] |} 'H :
   [main]sequent{ <H>; x:"assert"{beq_rat{'a;'b}}; <J[it]>;
                            y: 'a = 'b in rationals >- 'C[it]} -->
   [wf]sequent{ <H>; x:"assert"{beq_rat{'a;'b}}; <J[it]> >- 'a in rationals} -->
   [wf]sequent{ <H>; x:"assert"{beq_rat{'a;'b}}; <J[it]> >- 'b in rationals} -->
   sequent{ <H>; x:"assert"{beq_rat{'a;'b}}; <J['x]> >- 'C['x]}

interactive_rw beq_rat_is_true_rw :
   ('a = 'b in rationals) -->
   beq_rat{'a; 'b} <--> btrue

let beq_rat_is_trueC = beq_rat_is_true_rw

(*
 Derived from previous rewrite
 *)
interactive eq_2beq_rat {| intro [] |} :
   sequent { <H> >- 'a = 'b in rationals } -->
   sequent { <H> >- "assert"{beq_rat{'a; 'b}} }

interactive lt_bool_rat_member {| intro [] |} :
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
interactive lt_rat_decidable {| intro [] |} :
   [wf] sequent{ <H> >- 'a in rationals } -->
   [wf] sequent{ <H> >- 'b in rationals } -->
   sequent{ <H> >- decidable{('a < 'b)} }

interactive eq_rat_decidable {| intro [] |} :
   [wf] sequent{ <H> >- 'a in rationals } -->
   [wf] sequent{ <H> >- 'b in rationals } -->
   sequent{ <H> >- decidable{('a = 'b in rationals)} }

doc <:doc<
   @begin[doc]
   @modsubsection{Membership}

   The $Q$ type contains the @hrefterm[rat] terms.
   @end[doc]
>>
(*
 * H >- rat{'a;'b} = rat{'a;'b} in rationals
 * by numberEquality
 *)
prim ratEquality {| intro []; eqcd |} :
   [wf] sequent{ <H> >- 'a in int } -->
   [wf] sequent{ <H> >- 'b in posnat } -->
   sequent { <H> >- rat{'a;'b} in rationals } = it

doc <:doc<
   @begin[doc]
   @modsubsection{Order relation properties}

   <<lt_bool{'a;'b}>> defines irreflexive, asymmetric, transitive and
   discrete order on @tt[rationals]
   @end[doc]
>>

interactive lt_rat_Reflex :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   sequent { <H> >- band{lt_bool{'a; 'b}; lt_bool{'b; 'a}} ~ bfalse }

interactive_rw lt_rat_Reflex_rw {| reduce |} :
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   band{lt_bool{'a; 'b}; lt_bool{'b; 'a}} <--> bfalse

let lt_rat_ReflexC = lt_rat_Reflex_rw

interactive_rw lt_rat_irreflex_rw {| reduce |} :
   ( 'a in rationals ) -->
   lt_bool{'a;'a} <--> bfalse

let lt_rat_IrreflexC = lt_rat_irreflex_rw

interactive lt_rat_Asym 'a 'b :
   [main] sequent { <H> >- 'a < 'b } -->
   [main] sequent { <H> >- 'b < 'a } -->
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   sequent { <H> >- 'C }

let lt_rat_AsymT = lt_rat_Asym

interactive lt_rat_Trichot :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   sequent {
     <H> >- bor{bor{lt_bool{'a; 'b};lt_bool{'b; 'a}}; beq_int{'a; 'b}} ~ btrue
 }

interactive_rw lt_rat_Trichot_rw :
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   bor{bor{lt_bool{'a; 'b};lt_bool{'b; 'a}}; beq_int{'a; 'b}} <--> btrue

let lt_rat_TrichotC = lt_rat_Trichot_rw

let splitRationalsC a b =
   foldC
      (mk_bor_term
         (mk_bor_term
            (mk_lt_bool_term a b)
            (mk_lt_bool_term b a))
         (mk_beq_rat_term a b))
      lt_rat_TrichotC

interactive splitRationals 'a 'b :
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

let splitRationalsT = splitRationals

interactive lt_rat_Transit 'b :
   [main] sequent {
      <H> >- band{lt_bool{'a; 'b};lt_bool{'b; 'c}} = btrue in bool } -->
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   [wf] sequent { <H> >- 'c in rationals } -->
   sequent { <H> >- lt_bool{'a; 'c} ~ btrue }

interactive_rw lt_rat_Transit_rw 'b :
   ( band{lt_bool{'a; 'b};lt_bool{'b; 'c}} = btrue in bool ) -->
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   ( 'c in rationals ) -->
   lt_bool{'a; 'c} <--> btrue

let lt_rat_TransitC = lt_rat_Transit_rw

doc <:doc<
   @begin[doc]
   @modsubsection{Addition properties}

   @tt[add] is commutative and associative.

   @end[doc]
>>
interactive add_rat_Commut :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   sequent { <H> >- ('a +@ 'b) ~ ('b +@ 'a) }

interactive_rw add_rat_Commut_rw :
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   ('a +@ 'b) <--> ('b +@ 'a)

let add_rat_CommutC = add_rat_Commut_rw

interactive add_rat_Assoc :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   [wf] sequent { <H> >- 'c in rationals } -->
   sequent { <H> >- ('a +@ ('b +@ 'c)) ~ (('a +@ 'b) +@ 'c) }

interactive_rw add_rat_Assoc_rw :
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   ( 'c in rationals ) -->
   ('a +@ ('b +@ 'c)) <--> (('a +@ 'b) +@ 'c)

let add_rat_AssocC = add_rat_Assoc_rw

interactive_rw add_rat_Assoc2_rw {| reduce |} :
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   ( 'c in rationals ) -->
   (('a +@ 'b) +@ 'c) <--> ('a +@ ('b +@ 'c))

let add_rat_Assoc2C = add_rat_Assoc2_rw

doc <:doc<
   @begin[doc]

   0 is neutral element for @tt[add] in @tt[rationals]

   @end[doc]
>>
interactive add_rat_Id :
   [wf] sequent { <H> >- 'a in rationals } -->
   sequent { <H> >- ('a +@ 0) ~ 'a }

interactive_rw add_rat_Id_rw {| reduce |} :
   ( 'a in rationals ) -->
   ('a +@ 0) <--> 'a

let add_rat_IdC = add_rat_Id_rw

interactive_rw add_rat_Id2_rw {| reduce |} :
   ( 'a in rationals ) -->
   (0 +@ 'a) <--> 'a

let add_rat_Id2C = add_rat_Id2_rw

interactive_rw add_rat_Id3_rw :
   ( 'a in rationals ) -->
   'a <--> (0 +@ 'a)

let add_rat_Id3C = add_rat_Id3_rw

interactive_rw add_rat_Id4_rw :
   ( 'a in rationals ) -->
   'a <--> ('a +@ 0)

let add_rat_Id4C = add_rat_Id4_rw

doc <:doc<
   @begin[doc]

   Monotonicity:

   @end[doc]
>>
interactive lt_rat_addMono 'c :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   [wf] sequent { <H> >- 'c in rationals } -->
   sequent { <H> >- lt_bool{'a; 'b} ~ lt_bool{('a +@ 'c); ('b +@ 'c)} }

interactive_rw lt_rat_addMono_rw 'c :
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   ( 'c in rationals ) -->
   lt_bool{'a; 'b} <--> lt_bool{('a +@ 'c); ('b +@ 'c)}

let lt_rat_addMonoC = lt_rat_addMono_rw

interactive lt_rat_add_lt :
   [main] sequent { <H> >- 'a < 'b} -->
   [main] sequent { <H> >- 'c < 'd} -->
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   [wf] sequent { <H> >- 'c in rationals } -->
   [wf] sequent { <H> >- 'd in rationals } -->
   sequent { <H> >- ('a +@ 'c) < ('b +@ 'd) }

let lt_rat_add_ltT = lt_rat_add_lt

doc <:doc<
   @begin[doc]

   <<- 'a>> is an inverse element for <<'a>> in <<rationals>>

   @end[doc]
>>
interactive minus_rat_add_inverse :
   [wf] sequent { <H> >- 'a in rationals } -->
   sequent { <H> >- ( 'a +@ (- 'a ) ) ~ 0 }

interactive_rw minus_rat_add_inverse_rw {| reduce |} :
   ( 'a in rationals ) -->
   ( 'a +@ (- 'a) ) <--> 0

let minus_rat_add_inverseC = minus_rat_add_inverse_rw

interactive add_rat_Functionality 'c :
   [main] sequent { <H> >- ('a +@ 'c) ~ ('b +@ 'c) } -->
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   [wf] sequent { <H> >- 'c in rationals } -->
   sequent { <H> >- 'a ~ 'b }

interactive_rw add_rat_Functionality_rw 'b 'c :
   (('a +@ 'c) ~ ('b +@ 'c)) -->
   ('a in rationals) -->
   ('b in rationals) -->
   ('c in rationals) -->
   'a <--> 'b

let add_rat_FunctionalityC = add_rat_Functionality_rw

interactive minus_add_rat_Distrib :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   sequent { <H> >- (-('a +@ 'b)) ~ ((-'a) +@ (-'b)) }

interactive minus_minus_rat_reduce :
   [wf] sequent { <H> >- 'a in rationals } -->
   sequent { <H> >- (-(-'a)) ~ 'a }

interactive_rw minus_minus_rat_reduce_rw {| reduce |} :
   ('a in rationals) -->
   (-(-'a)) <--> 'a

let minus_minus_rat_reduceC = minus_minus_rat_reduce_rw

interactive_rw minus_same_rat_rw {| reduce |} :
   ('a in rationals) -->
   ('a -@ 'a) <--> 0

interactive_rw plus_minus_rat_rw {| reduce |} :
   ('a in rationals) -->
   ('b in rationals) -->
   (('a +@ 'b) -@ 'b) <--> 'a

interactive_rw minus_plus_rat_rw {| reduce |} :
   ('a in rationals) -->
   ('b in rationals) -->
   (('a -@ 'b) +@ 'b) <--> 'a

(***********************************************************
 * TYPE INFERENCE
 ***********************************************************)

(*
 * Type of rationals and of number
 *)
let resource typeinf += [
   (<<rationals>>, infer_univ1);
   (<<rat{'a;'b}>>, Typeinf.infer_const <<rationals>>)
]

doc <:doc< @docoff >>