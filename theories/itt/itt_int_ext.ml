doc <:doc<
   @spelling{gt_bool le_bool ge_bool gt le ge nequal}

   @begin[doc]
   @module[Itt_int_ext]

   Here we define multiplicative operations on integers
   (<<Perv!nil *@ Perv!nil>>, <<Perv!nil /@ Perv!nil>>,
   <<Perv!nil %@ Perv!nil>>)
   and the rest of traditional inequalities both in propositional
   (<<Perv!nil > Perv!nil>>, <<Perv!nil <= Perv!nil>>, <<Perv!nil >= Perv!nil>>,
   <<nequal{(Perv!nil) ; (Perv!nil)}>>) and boolean
   (<<gt_bool{(Perv!nil) ; (Perv!nil)}>>, <<le_bool{(Perv!nil) ; (Perv!nil)}>>,
   <<ge_bool{(Perv!nil) ; (Perv!nil)}>>, <<bneq_int{(Perv!nil) ; (Perv!nil)}>>) forms.
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

doc <:doc< @doc{@parents} >>
extends Itt_equal
extends Itt_rfun
extends Itt_logic
extends Itt_bool
extends Itt_int_base
doc docoff

open Printf
open Lm_debug
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermType
open Refiner.Refiner.RefineError
open Rformat
open Mp_resource

open Var
open Tactic_type
open Tactic_type.Tacticals

open Base_meta
open Dtactic
open Auto_tactic
open Top_conversionals

open Itt_equal
open Itt_struct
open Itt_squash
open Itt_bool
open Itt_int_base

let _ = show_loading "Loading Itt_int_ext%t"
(************************************************************************
 * TERMS                                                                *
 ************************************************************************)
doc <:doc<
   @begin[doc]
   @terms
   Multiplicative operations on <<int>>
   @end[doc]
>>
declare "mul"{'a; 'b}
declare "div"{'a; 'b}
declare "rem"{'a; 'b}

(*
 Definitions of >b <=b >=b
 *)

doc <:doc< @doc{More boolean inequalities} >>

define unfold_gt_bool {| reduce |} :
   gt_bool{'a; 'b} <--> lt_bool{'b; 'a}

define unfold_le_bool :
   le_bool{'a; 'b} <--> bnot{lt_bool{'b; 'a}}

define unfold_ge_bool :
   ge_bool{'a; 'b} <--> bnot{lt_bool{'a; 'b}}

define unfold_bneq_int :
   bneq_int{'a; 'b} <--> bnot{beq_int{'a; 'b}}

let bneq_int_term = << bneq_int{'x; 'y} >>
let bneq_int_opname = opname_of_term bneq_int_term
let is_bneq_int_term = is_dep0_dep0_term bneq_int_opname
let mk_bneq_int_term = mk_dep0_dep0_term bneq_int_opname
let dest_bneq_int = dest_dep0_dep0_term bneq_int_opname

doc docoff

let resource reduce += [
   << bnot{lt_bool{'b; 'a}} >>, (makeFoldC << le_bool{'a;'b} >> unfold_le_bool);
   << bnot{le_bool{'a; 'b}} >>, (addrC [0] unfold_le_bool);
(*    << le_bool{'a; 'b} >>, unfold_le_bool;
   << ge_bool{'a; 'b} >>, unfold_ge_bool;
   << bneq_int{'a; 'b} >>, unfold_bneq_int;
*)
   << le_bool{'a;'a}>>, (unfold_le_bool thenC (addrC [0] lt_IrreflexC));
   << ge_bool{'a;'a}>>, (unfold_ge_bool thenC (addrC [0] lt_IrreflexC));
]

(*
 Prop-int-relations definitions
 *)

define unfold_gt {| reduce |} :
   gt{'a; 'b} <--> ('b < 'a)

let mul_term = << 'x *@ 'y >>
let mul_opname = opname_of_term mul_term
let is_mul_term = is_dep0_dep0_term mul_opname
let mk_mul_term = mk_dep0_dep0_term mul_opname
let dest_mul = dest_dep0_dep0_term mul_opname

let div_term = << 'x /@ 'y >>
let div_opname = opname_of_term div_term
let is_div_term = is_dep0_dep0_term div_opname
let mk_div_term = mk_dep0_dep0_term div_opname
let dest_div = dest_dep0_dep0_term div_opname

let rem_term = << "rem"{'x; 'y} >>
let rem_opname = opname_of_term rem_term
let is_rem_term = is_dep0_dep0_term rem_opname
let mk_rem_term = mk_dep0_dep0_term rem_opname
let dest_rem = dest_dep0_dep0_term rem_opname

let gt_term = << 'x > 'y >>
let gt_opname = opname_of_term gt_term
let is_gt_term = is_dep0_dep0_term gt_opname
let mk_gt_term = mk_dep0_dep0_term gt_opname
let dest_gt = dest_dep0_dep0_term gt_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_mul

dform mul_df1 : except_mode[src] :: parens :: "prec"[prec_mul] :: "mul"{'a; 'b}
 =
   slot["lt"]{'a} `" * " slot["le"]{'b}
dform mul_df2 : mode[src] :: parens :: "prec"[prec_mul] :: "mul"{'a; 'b} =
   slot["lt"]{'a} `" *@ " slot["le"]{'b}

dform div_df1 : except_mode[src] :: parens :: "prec"[prec_mul] :: "div"{'a; 'b}
 =
   slot["lt"]{'a} Nuprl_font!"div" slot["le"]{'b}
dform div_df2 : mode[src] :: parens :: "prec"[prec_mul] :: "div"{'a; 'b} =
   slot["lt"]{'a} `" /@ " slot["le"]{'b}

dform rem_df1 : except_mode[src] :: parens :: "prec"[prec_mul] :: "rem"{'a; 'b}
 =
   slot["lt"]{'a} `" % " slot["le"]{'b}
dform rem_df2 : mode[src] :: parens :: "prec"[prec_mul] :: "rem"{'a; 'b} =
   slot["lt"]{'a} `" %@ " slot["le"]{'b}

dform gt_df1 : parens :: "prec"[prec_compare] :: gt{'a; 'b} =
   slot["lt"]{'a} `" > " slot["le"]{'b}

doc <:doc<
	@begin[doc]
   More propositional inequalities.
   As it was said in @hrefmodule[Itt_int_base], we define propositional inequalities
   via correspondent boolean inequalities.
	@end[doc]
>>

define unfold_le :
   le{'a; 'b} <--> "assert"{le_bool{'a; 'b}}

define unfold_ge {| reduce |} :
   ge{'a; 'b} <--> ('b <= 'a)

define unfold_neq_int :
   nequal{'a; 'b} <--> "assert"{bneq_int{'a; 'b}}

doc <:doc< @docoff >>

let resource reduce += [
   <<number[i:n] <= number[j:n]>>, (unfold_le thenC
                                   (addrC [0] (unfold_le_bool thenC
                                   (addrC [0] reduce_lt))));
   <<nequal{number[i:n]; number[j:n]}>>, (unfold_neq_int thenC
                                         (addrC [0] (unfold_bneq_int thenC
					 (addrC [0] reduce_eq_int))));
(*
   << le{'a; 'b} >>, unfold_le;
   << nequal{'a; 'b} >>, unfold_neq_int;
*)
   << le{'a;'a}>>, (unfold_le thenC (addrC [0] (unfold_le_bool thenC (addrC [0] lt_IrreflexC))));
]

let le_term = << 'x <= 'y >>
let le_opname = opname_of_term le_term
let is_le_term = is_dep0_dep0_term le_opname
let mk_le_term = mk_dep0_dep0_term le_opname
let dest_le = dest_dep0_dep0_term le_opname

let ge_term = << 'x >= 'y >>
let ge_opname = opname_of_term ge_term
let is_ge_term = is_dep0_dep0_term ge_opname
let mk_ge_term = mk_dep0_dep0_term ge_opname
let dest_ge = dest_dep0_dep0_term ge_opname

let neq_int_term = << nequal{'x; 'y} >>
let neq_int_opname = opname_of_term neq_int_term
let is_neq_int_term = is_dep0_dep0_term neq_int_opname
let mk_neq_int_term = mk_dep0_dep0_term neq_int_opname
let dest_neq_int = dest_dep0_dep0_term neq_int_opname

dform le_df1 : except_mode[src] :: parens :: "prec"[prec_compare] :: le{'a; 'b}
 =
   slot["lt"]{'a} Nuprl_font!le slot["le"]{'b}
dform le_df2 : mode[src] :: parens :: "prec"[prec_compare] :: le{'a; 'b} =
   slot["lt"]{'a} `" <= " slot["le"]{'b}

dform ge_df1 : except_mode[src] :: parens :: "prec"[prec_compare] :: ge{'a; 'b}
 =
   slot["lt"]{'a} Nuprl_font!ge slot["le"]{'b}
dform ge_df2 : mode[src] :: parens :: "prec"[prec_compare] :: ge{'a; 'b} =
   slot["lt"]{'a} `" >= " slot["le"]{'b}

dform bneq_int_df1 : parens :: "prec"[prec_compare] :: bneq_int{'a; 'b} =
   slot["lt"]{'a} `" " Nuprl_font!neq Nuprl_font!subb `" " slot["le"]{'b}

dform le_bool_df1 : parens :: "prec"[prec_compare] :: le_bool{'a; 'b} =
   slot["lt"]{'a} `" " Nuprl_font!le Nuprl_font!subb `" " slot["le"]{'b}

dform gt_bool_df1 : parens :: "prec"[prec_compare] :: gt_bool{'a; 'b} =
   slot["lt"]{'a} `" >" Nuprl_font!subb `" " slot["le"]{'b}

dform ge_bool_df1 : parens :: "prec"[prec_compare] :: ge_bool{'a; 'b} =
   slot["lt"]{'a} `" " Nuprl_font!ge Nuprl_font!subb `" " slot["le"]{'b}

dform nequal_df1 : parens :: "prec"[prec_compare] :: nequal{'a; 'b} =
   slot["lt"]{'a} `" " Nuprl_font!neq `" " slot["le"]{'b}

doc <:doc< @doc{Integer segmentation} >>

define unfold_int_seg : int_seg{'i; 'j} <--> {x:int | 'x >= 'i & 'x < 'j}

doc <:doc< @docoff >>

dform intSeg_df1 : except_mode [src] :: except_mode [prl] :: int_seg{'i; 'j} =
   `"{" slot{'i} `".." slot{'j} sup["-":s] `"}"

dform intSeg_df1 : mode [prl] :: int_seg{'i; 'j} =
   `"{" slot{'i} `"..(" slot{'j} `"-1)}"

let fold_int_seg = makeFoldC << int_seg{'i; 'j} >> unfold_int_seg

doc <:doc<
   @begin[doc]
   @modsection{Rules and rewrites}
   @modsubsection{Operations on literals}

   The binary arithmetic operators on literal integers are defined using the
   the @emph{meta} arithmetic operators that are @MetaPRL
   builtin operations.
   @end[doc]
>>

prim_rw reduce_mul_meta : (number[i:n] *@ number[j:n]) <-->
   number{meta_prod[i:n, j:n]}
prim_rw reduce_div_meta : (number[i:n] /@ number[j:n]) <-->
   number{meta_quot[i:n, j:n]}
prim_rw reduce_rem_meta : "rem"{number[i:n]; number[j:n]} <-->
   number{meta_rem[i:n, j:n]}

doc <:doc< @docoff >>

let reduce_mul =
   reduce_mul_meta thenC (addrC [0] reduce_meta_prod) thenC reduce_numeral

let reduce_div =
   reduce_div_meta thenC (addrC [0] reduce_meta_quot) thenC reduce_numeral

let reduce_rem =
   reduce_rem_meta thenC (addrC [0] reduce_meta_rem) thenC reduce_numeral

let resource reduce += [
   <<number[i:n] *@ number[j:n]>>, reduce_mul;
   <<number[i:n] /@ number[j:n]>>, reduce_div;
   <<"rem"{number[i:n]; number[j:n]}>>, reduce_rem;
]

doc <:doc<
   @begin[doc]
   @modsubsection{Well-formedness of inequalities}

   @end[doc]
>>

interactive gt_bool_wf {| intro [complete_unless_member]; eqcd |} :
   [wf] sequent { <H> >- 'a1='a2 in int } -->
   [wf] sequent { <H> >- 'b1='b2 in int } -->
   sequent { <H> >- gt_bool{'a1; 'b1}=gt_bool{'a2; 'b2} in bool }

interactive le_bool_wf {| intro [complete_unless_member]; eqcd |} :
   [wf] sequent { <H> >- 'a1='a2 in int } -->
   [wf] sequent { <H> >- 'b1='b2 in int } -->
   sequent { <H> >- le_bool{'a1; 'b1}=le_bool{'a2; 'b2} in bool }

interactive ge_bool_wf {| intro [complete_unless_member]; eqcd |} :
   [wf] sequent { <H> >- 'a1='a2 in int } -->
   [wf] sequent { <H> >- 'b1='b2 in int } -->
   sequent { <H> >- ge_bool{'a1; 'b1}=ge_bool{'a2; 'b2} in bool }

interactive bneq_int_wf {| intro [complete_unless_member]; eqcd |} :
   [wf] sequent { <H> >- 'a1='a2 in int } -->
   [wf] sequent { <H> >- 'b1='b2 in int } -->
   sequent { <H> >- bneq_int{'a1; 'b1}=bneq_int{'a2; 'b2} in bool }

interactive gt_wf {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- "type"{gt{'a; 'b}} }

interactive le_wf {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- "type"{le{'a; 'b}} }

interactive ge_wf {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- "type"{ge{'a; 'b}} }

interactive ge_sqstable {| squash; intro [] |} :
   sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- it in ('a >= 'b) }

doc <:doc<
   @begin[doc]
   @modsection{Well-formedness and algebraic properties of <<(Perv!nil) *@ (Perv!nil)>>}
   @end[doc]
>>

prim mul_wf {| intro [complete_unless_member]; eqcd |} :
   [wf] sequent { <H> >- 'a = 'a1 in int } -->
   [wf] sequent { <H> >- 'b = 'b1 in int } -->
   sequent { <H> >- 'a *@ 'b = 'a1 *@ 'b1 in int } = it

prim mul_Commut :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a *@ 'b) ~ ('b *@ 'a) } = it

interactive_rw mul_Commut_rw :
   ('a in int) -->
   ('b in int) -->
   ('a *@ 'b) <--> ('b *@ 'a)

let mul_CommutC = mul_Commut_rw

prim mul_Assoc :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ('a *@ ('b *@ 'c)) ~ (('a *@ 'b) *@ 'c) } = it

interactive_rw mul_Assoc_rw :
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   ('a *@ ('b *@ 'c)) <--> (('a *@ 'b) *@ 'c)

let mul_AssocC = mul_Assoc_rw

interactive_rw mul_Assoc2_rw :
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   (('a *@ 'b) *@ 'c) <--> ('a *@ ('b *@ 'c))

let mul_Assoc2C = mul_Assoc2_rw

prim mul_add_Distrib :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ('a *@ ('b +@ 'c)) ~ (('a *@ 'b) +@ ('a *@ 'c)) } = it

interactive_rw mul_add_Distrib_rw :
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   ('a *@ ('b +@ 'c)) <--> (('a *@ 'b) +@ ('a *@ 'c))

let mul_add_DistribC = mul_add_Distrib_rw

prim mul_Id :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- (1 *@ 'a) ~ 'a } = it

interactive_rw mul_Id_rw :
   ('a in int) -->
   (1 *@ 'a) <--> 'a

let mul_IdC = mul_Id_rw

interactive mul_Id2 :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- ('a *@ 1) ~ 'a }

interactive_rw mul_Id2_rw :
   ('a in int) -->
   ('a *@ 1) <--> 'a

let mul_Id2C = mul_Id2_rw

interactive mul_Id3 :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- 'a ~ (1 *@ 'a) }

interactive_rw mul_Id3_rw :
   ('a in int) -->
   'a <--> (1 *@ 'a)

let mul_Id3C = mul_Id3_rw

prim mul_Zero :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- (0 *@ 'a) ~ 0 } = it

interactive_rw mul_Zero_rw :
   ('a in int) -->
   (0 *@ 'a) <--> 0

let mul_ZeroC = mul_Zero_rw

interactive mul_Zero2 :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- ('a *@ 0) ~ 0 }

interactive_rw mul_Zero2_rw :
   ('a in int) -->
   ('a *@ 0) <--> 0

let mul_Zero2C = mul_Zero2_rw

interactive lt_mulPositMonoEq 'c :
   sequent { <H> >- 0 < 'c } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- lt_bool{'a; 'b} = lt_bool{('c *@ 'a); ('c *@ 'b) } in
 bool }

interactive lt_mulPositMono 'c :
   sequent { <H> >- 0 < 'c } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- lt_bool{'a; 'b} ~ lt_bool{('c *@ 'a); ('c *@ 'b) } }

interactive_rw lt_mulPositMono_rw 'c :
   (0 < 'c) -->
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   lt_bool{'a; 'b} <--> lt_bool{('c *@ 'a); ('c *@ 'b) }

let lt_mulPositMonoC = lt_mulPositMono_rw

interactive mul_uni_Assoc :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a *@ (- 'b)) ~ ((- 'a) *@ 'b) }

interactive_rw mul_uni_Assoc_rw :
   ('a in int) -->
   ('b in int) -->
   ('a *@ (- 'b)) <--> ((- 'a) *@ 'b)

let mul_uni_AssocC = mul_uni_Assoc_rw

interactive lt_mulNegMono 'c :
   sequent { <H> >- 'c < 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- lt_bool{'a; 'b} ~ lt_bool{('c *@ 'b) ; ('c *@ 'a)} }

interactive_rw lt_mulNegMono_rw 'c :
   ('c < 0)  -->
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   lt_bool{'a; 'b} <--> lt_bool{('c *@ 'b) ; ('c *@ 'a)}

let lt_mulNegMonoC = lt_mulNegMono_rw

doc <:doc<
   @begin[doc]
   @modsection{Definition and well-formedness of <<Perv!nil %@ Perv!nil>>}
   @end[doc]
>>
prim rem_baseReduce :
   sequent { <H> >- 0 <= 'a } -->
   sequent { <H> >- 'a < 'b } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a %@ 'b) ~ 'a } = it

interactive_rw rem_baseReduce_rw :
   (0 <= 'a) -->
   ('a < 'b) -->
   ('a in int) -->
   ('b in int) -->
   ('a %@ 'b) <--> 'a

let rem_baseReduceC = rem_baseReduce_rw

prim rem_indReduce :
   sequent { <H> >- 0 < 'b } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ((('a *@ 'b) +@ 'c) %@ 'b) ~ ('c %@ 'b) } = it

interactive_rw rem_indReduce_rw :
   (0 < 'b) -->
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   ((('a *@ 'b) +@ 'c) %@ 'b) <--> ('c %@ 'b)

let rem_indReduceC = rem_indReduce_rw

interactive rem_wf {| intro []; eqcd |} :
   sequent { <H> >- "nequal"{'b ; 0} } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a %@ 'b) in int }

doc <:doc<
   @begin[doc]
   @modsection{Definition and properties of <<Perv!nil /@ Perv!nil>>}
   @end[doc]
>>
prim div_baseReduce :
   sequent { <H> >- 0 <= 'a } -->
   sequent { <H> >- 'a < 'b } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a /@ 'b) ~ 0 } = it

interactive_rw div_baseReduce_rw :
   (0 <= 'a) -->
   ('a < 'b) -->
   ('a in int) -->
   ('b in int) -->
   ('a /@ 'b) <--> 0

let div_baseReduceC = div_baseReduce_rw

prim div_indReduce :
   sequent { <H> >- 0 < 'b } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ((('a *@ 'b) +@ 'c) /@ 'b) ~ ('a +@ ('c /@ 'b)) } = it

interactive_rw div_indReduce_rw :
   (0 < 'b) -->
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   ((('a *@ 'b) +@ 'c) /@ 'b) <--> ('a +@ ('c /@ 'b))

let div_indReduceC = div_indReduce_rw

interactive div_wf {| intro []; eqcd |} :
   sequent { <H> >- "nequal"{'b ; 0} } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- 'a /@ 'b in int }

interactive lt_divMono 'b :
   sequent { <H> >- 0 < 'c } -->
   sequent { <H> >- 'a < 'b } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- 'a /@ 'c <= 'b /@ 'c }

interactive add_divReduce :
   sequent { <H> >- 0 < 'a } -->
   sequent { <H> >- 0 < 'b } -->
   sequent { <H> >- 0 < 'c } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ('a /@ 'c) +@ ('b /@ 'c) <= ('a +@ 'b) /@ 'c }

interactive div_Assoc :
   sequent { <H> >- 0 <= 'a } -->
   sequent { <H> >- 0 < 'b } -->
   sequent { <H> >- 0 < 'c } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- (('a /@ 'b) /@ 'c) ~ ('a /@ ('b *@ 'c)) }

interactive_rw div_Assoc_rw :
   (0 <= 'a) -->
   (0 < 'b) -->
   (0 < 'c) -->
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   (('a /@ 'b) /@ 'c) <--> ('a /@ ('b *@ 'c))

let div_AssocC = div_Assoc_rw

doc <:doc<
   @begin[doc]
   @modsection{Integer segmentation properties}
   @end[doc]
>>
interactive intSegType {| intro [] |} :
   sequent { <H> >- 'i in int} -->
   sequent { <H> >- 'j in int} -->
   sequent { <H> >- "type"{int_seg{'i; 'j}} }

interactive intSegMemberEquality {| intro [] |} :
   sequent { <H> >- 'i in int} -->
   sequent { <H> >- 'j in int} -->
   sequent { <H> >- 'a = 'b in int} -->
   sequent { <H> >- 'a >= 'i}  -->
   sequent { <H> >- 'a < 'j}  -->
   sequent { <H> >- 'a = 'b in int_seg{'i; 'j} }

interactive intSegElimination {| elim [] |} 'H :
   sequent { <H>; x: int_seg{'i; 'j}; <J['x]> >- 'i in int } -->
   sequent { <H>; x: int_seg{'i; 'j}; <J['x]> >- 'j in int } -->
   sequent { <H>; x: int; v:'x >= 'i; w: 'x < 'j; <J['x]> >- 'C['x] }  -->
   sequent { <H>; x: int_seg{'i; 'j}; <J['x]> >- 'C['x] }

doc <:doc< @docoff >>

(*
Incorrect but there has to be some assoc/commut/composition property

rewrite rem_Assoc :
   sequent { <H> >- 0 <= 'a } -->
   sequent { <H> >- 0 < 'b } -->
   sequent { <H> >- 0 < 'c } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ('a %@ 'b) %@ 'c <--> ('a %@ 'c) %@ 'b }

*)

let resource reduce +=
   [<< (('a *@ 'b) *@ 'c) >>, mul_Assoc2_rw;
    << ('a *@ ('b +@ 'c)) >>, mul_add_Distrib_rw;
    << (1 *@ 'a) >>, mul_Id_rw;
    << ('a *@ 1) >>, mul_Id2_rw;
    << (0 *@ 'a) >>, mul_Zero_rw;
    << ('a *@ 0) >>, mul_Zero2_rw;
    << ('a *@ (- 'b)) >>, mul_uni_Assoc_rw]
