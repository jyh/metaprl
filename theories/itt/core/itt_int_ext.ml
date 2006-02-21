doc <:doc<
   @module[Itt_int_ext]

   Here we define multiplicative operations on integers
   (<<'x *@ 'x>>, <<'x /@ 'x>>,
   <<'x %@ 'x>>)
   and the rest of traditional inequalities both in propositional
   (<<'x > 'x>>, <<'x <= 'x>>, <<'x >= 'x>>,
   <<nequal{('x) ; ('x)}>>) and boolean
   (<<gt_bool{('x) ; ('x)}>>, <<le_bool{('x) ; ('x)}>>,
   <<ge_bool{('x) ; ('x)}>>, <<bneq_int{('x) ; ('x)}>>) forms.

   Note that both ``less then or equal'' forms are implemented as input forms
   that turn them into appropriate ``greater then or equal'' forms and similarly
   ``greater than'' forms will simply turn into corresponding ``less then'' ones.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998-2006 MetaPRL Group, Cornell University, Moscow State
   University, City University of New York, and California Institute of Technology

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

   Author: Yegor Bryukhov @email{ynb@mail.ru}
   Modified by: Aleksey Nogin @email{nogin@cs.caltech.edu}
   @end[license]
>>

doc <:doc< @parents >>
extends Itt_equal
extends Itt_dfun
extends Itt_logic
extends Itt_bool
extends Itt_int_base
doc docoff

open Lm_debug
open Lm_printf

open Basic_tactics
open Base_meta

open Itt_equal
open Itt_struct
open Itt_squash
open Itt_bool
open Itt_int_base

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)
doc <:doc<
   @terms
   Multiplicative operations on <<int>>
>>
define (*private*) unfold_mul : "mul"{'a; 'b} <--> ind{'a; m, z. 'z -@ 'b; 0; m, z. 'z +@ 'b }
declare "div"{'a; 'b}
declare "rem"{'a; 'b}

(*
 Definitions of >b <=b >=b
 *)

doc <:doc< More boolean inequalities >>

define unfold_ge_bool :
   ge_bool{'a; 'b} <--> bnot{lt_bool{'a; 'b}}

define iform unfold_bneq_int :
   bneq_int{'a; 'b} <--> bnot{beq_int{'a; 'b}}

doc docoff

let resource reduce += [
   << bnot{lt_bool{'a; 'b}} >>, wrap_reduce (makeFoldC << ge_bool{'a;'b} >> unfold_ge_bool);
   << bnot{ge_bool{'a; 'b}} >>,
      wrap_reduce_crw (addrC [Subterm 1]
         (addrC [Subterm 1] reduceC thenC addrC [Subterm 2] reduceC thenC unfold_ge_bool)
       thenC Itt_bool.reduce_bnot_bnotC);
   << ge_bool{'a;'a}>>, wrap_reduce_crw (unfold_ge_bool thenC (addrC [Subterm 1] lt_IrreflexC));
]

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

let bneq_int_term = << bneq_int{'x; 'y} >>
let bneq_int_opname = opname_of_term bneq_int_term
let is_bneq_int_term = is_dep0_dep0_term bneq_int_opname
let mk_bneq_int_term = mk_dep0_dep0_term bneq_int_opname
let dest_bneq_int = dest_dep0_dep0_term bneq_int_opname

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

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

(*
 * XXX: TODO: Once comments on terms or soft abstractions are implemented (bugs 256/261),
 *            the "le" forms should have a comment that makes sure they will be displayed
 *            as "le".
 *)
define iform le_bool_iform: le_bool{'a; 'b} <--> ge_bool{'b; 'a}
define iform gt_bool_iform: gt_bool{'a; 'b} <--> lt_bool{'b; 'a}
define iform le_iform: le{'a; 'b} <--> ge{'b; 'a}
define iform gt_iform: gt{'a; 'b} <--> lt{'b; 'a}

prec prec_mul

dform mul_df1 : except_mode[src] :: parens :: "prec"[prec_mul] :: "mul"{'a; 'b}
 =
   slot["lt"]{'a} `" * " slot["le"]{'b}
dform mul_df2 : mode[src] :: parens :: "prec"[prec_mul] :: "mul"{'a; 'b} =
   slot["lt"]{'a} `" *@ " slot["le"]{'b}

dform div_df1 : except_mode[src] :: parens :: "prec"[prec_mul] :: "div"{'a; 'b}
 =
   slot["lt"]{'a} Mpsymbols!"div" slot["le"]{'b}
dform div_df2 : mode[src] :: parens :: "prec"[prec_mul] :: "div"{'a; 'b} =
   slot["lt"]{'a} `" /@ " slot["le"]{'b}

dform rem_df1 : except_mode[src] :: parens :: "prec"[prec_mul] :: "rem"{'a; 'b}
 =
   slot["lt"]{'a} `" % " slot["le"]{'b}
dform rem_df2 : mode[src] :: parens :: "prec"[prec_mul] :: "rem"{'a; 'b} =
   slot["lt"]{'a} `" %@ " slot["le"]{'b}

dform gt_df1 : parens :: "prec"[prec_compare] :: gt{'a; number[n:n]} =
   slot["lt"]{'a} `" > " slot["le"]{number[n:n]}

doc <:doc<
   More propositional inequalities.
   As it was said in @hrefmodule[Itt_int_base], we define propositional inequalities
   via correspondent boolean inequalities.
>>

define unfold_ge :
   ge{'a; 'b} <--> "assert"{ge_bool{'a; 'b}}

define unfold_neq_int :
   nequal{'a; 'b} <--> "assert"{bneq_int{'a; 'b}}

doc docoff

let fold_ge = makeFoldC << ge{'a; 'b} >> unfold_ge
let fold_neq_int = makeFoldC << nequal{'a; 'b} >> unfold_neq_int

let reduce_ge_prop = (unfold_ge thenC
                     (addrC [Subterm 1] (unfold_ge_bool thenC
                     (addrC [Subterm 1] reduce_lt))))
let reduce_neq_prop = unfold_neq_int thenC
                      (addrC [Subterm 1; Subterm 1] reduce_eq_int)

let resource reduce += [
	<<number[i:n] >= number[j:n]>>, wrap_reduce reduce_ge_prop;
   <<nequal{number[i:n]; number[j:n]}>>, wrap_reduce reduce_neq_prop;
   <<"assert"{ge_bool{'a; 'b}}>>, wrap_reduce fold_ge;
   <<"assert"{bneq_int{'a; 'b}}>>, wrap_reduce fold_neq_int;
   << ge{'a;'a} >>, wrap_reduce_crw
      (unfold_ge thenC (addrC [Subterm 1] (unfold_ge_bool thenC (addrC [Subterm 1] lt_IrreflexC))));
]

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

let dest_geT = argfunT (fun i p ->
   let t = if i = 0 then concl p else nth_hyp p i in
      (rw (
         if is_ge_term t then 
            unfold_ge thenC (addrC [Subterm 1] unfold_ge_bool)
         else
            addrC [Subterm 1] unfold_ge_bool) i)
      thenT (if i = 0 then assert_bnot_intro taa else assert_bnot_elim i))

(*
 * XXX: TODO: Once comments on terms or soft abstractions are implemented (bugs 256/261),
 *            the "le"/"gt" forms should have a comment that makes sure they will be displayed
 *            as "le"/"gt".
 *)
dform le_df1 : except_mode[src] :: parens :: "prec"[prec_compare] :: le{'a; number[n:n]}
 =
   slot["lt"]{'a} Mpsymbols!le slot["le"]{number[n:n]}

dform le_df2 : mode[src] :: parens :: "prec"[prec_compare] :: le{'a; number[n:n]} =
   slot["lt"]{'a} `" <=" space slot["le"]{number[n:n]}

dform le_bool_df1 : parens :: "prec"[prec_compare] :: le_bool{'a; number[n:n]} =
   slot["lt"]{'a} `" " Mpsymbols!le Mpsymbols!subb `" " slot["le"]{number[n:n]}

dform ge_df1 : except_mode[src] :: parens :: "prec"[prec_compare] :: ge{'a; 'b}
 =
   slot["lt"]{'a} Mpsymbols!ge slot["le"]{'b}
dform ge_df2 : mode[src] :: parens :: "prec"[prec_compare] :: ge{'a; 'b} =
   slot["lt"]{'a} `" >= " slot["le"]{'b}

dform bneq_int_df1 : parens :: "prec"[prec_compare] :: bneq_int{'a; 'b} =
   slot["lt"]{'a} `" " Mpsymbols!neq Mpsymbols!subb `" " slot["le"]{'b}

dform gt_bool_df1 : parens :: "prec"[prec_compare] :: gt_bool{'a; number[n:n]} =
   slot["lt"]{'a} `" >" Mpsymbols!subb `" " slot["le"]{number[n:n]}

dform ge_bool_df1 : parens :: "prec"[prec_compare] :: ge_bool{'a; 'b} =
   slot["lt"]{'a} `" " Mpsymbols!ge Mpsymbols!subb `" " slot["le"]{'b}

dform nequal_df1 : parens :: "prec"[prec_compare] :: nequal{'a; 'b} =
   slot["lt"]{'a} `" " Mpsymbols!neq `" " slot["le"]{'b}

doc <:doc< Integer segmentation >>

define unfold_int_seg : int_seg{'i; 'j} <--> {x:int | 'x >= 'i & 'x < 'j}

doc docoff

dform intSeg_df1 : except_mode [src] :: except_mode [prl] :: int_seg{'i; 'j} =
   `"{" slot{'i} `".." slot{'j} sup["-":s] `"}"

dform intSeg_df1 : mode [prl] :: int_seg{'i; 'j} =
   `"{" slot{'i} `"..(" slot{'j} `"-1)}"

let fold_int_seg = makeFoldC << int_seg{'i; 'j} >> unfold_int_seg

define unfold_max: max{'i;'j} <--> if 'i<@ 'j then 'j else 'i

define unfold_min: min{'i;'j} <--> if 'i<@ 'j then 'i else 'j

dform max_df : except_mode [src] :: max{'i; 'j} = `"max" `"(" 'i `"; " 'j ")"

dform min_df : except_mode [src] :: min{'i; 'j} = `"min" `"(" 'i `"; " 'j ")"

define unfold_abs : abs{'a} <--> ind{'a;x,y.(-'a);0;x,y.'a}
(*if 'a <@ 0 then -'a else 'a*)

define unfold_sign : sign{'a} <--> ind{'a;x,y.(-1);0;x,y.1}
(*if 'a <@ 0 then number[(-1):n] else if 0 <@ 'a then 1 else 0*)

doc <:doc<
   @modsection{Rules and rewrites}
   @modsubsection{Operations on literals}

   The binary arithmetic operators on literal integers are defined using the
   the @emph{meta} arithmetic operators that are @MetaPRL
   builtin operations.
>>

prim_rw reduce_mul_meta : (number[i:n] *@ number[j:n]) <-->
   number{meta_prod[i:n, j:n]}
prim_rw reduce_div_meta : (number[i:n] /@ number[j:n]) <-->
   number{meta_quot[i:n, j:n]}
prim_rw reduce_rem_meta : "rem"{number[i:n]; number[j:n]} <-->
   number{meta_rem[i:n, j:n]}

doc docoff

let reduce_mul =
   reduce_mul_meta thenC (addrC [Subterm 1] reduce_meta_prod) thenC reduce_numeral

let reduce_div =
   reduce_div_meta thenC (addrC [Subterm 1] reduce_meta_quot) thenC reduce_numeral

let reduce_rem =
   reduce_rem_meta thenC (addrC [Subterm 1] reduce_meta_rem) thenC reduce_numeral

let resource arith_unfold += [
   <<number[i:n] *@ number[j:n]>>, reduce_mul;
]

let resource reduce += [
   <<number[i:n] *@ number[j:n]>>, wrap_reduce reduce_mul;
   <<number[i:n] /@ number[j:n]>>, wrap_reduce reduce_div;
   <<"rem"{number[i:n]; number[j:n]}>>, wrap_reduce reduce_rem;
	<<max{number[i:n]; number[j:n]}>>, wrap_reduce unfold_max;
	<<min{number[i:n]; number[j:n]}>>, wrap_reduce unfold_min;
]

doc <:doc<
   @modsubsection{Well-formedness of inequalities}

>>
interactive le_bool_wf {| intro [complete_unless_member] |} :
   [wf] sequent { <H> >- 'a1='a2 in int } -->
   [wf] sequent { <H> >- 'b1='b2 in int } -->
   sequent { <H> >- le_bool{'a1; 'b1}=le_bool{'a2; 'b2} in bool }

interactive ge_bool_wf {| intro [complete_unless_member] |} :
   [wf] sequent { <H> >- 'a1='a2 in int } -->
   [wf] sequent { <H> >- 'b1='b2 in int } -->
   sequent { <H> >- ge_bool{'a1; 'b1}=ge_bool{'a2; 'b2} in bool }

interactive neq_wf {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- "type"{'a <> 'b} }

interactive le_wf {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- "type"{le{'a; 'b}} }

interactive ge_wf {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- "type"{ge{'a; 'b}} }

interactive beq_int_is_false :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'a <> 'b } -->
   sequent { <H> >- beq_int{'a; 'b} ~ bfalse }

interactive_rw beq_int_is_false_rw :
   ('a in int) -->
   ('b in int) -->
   ('a <> 'b) -->
   beq_int{'a; 'b} <--> bfalse

let beq_int_is_falseC = beq_int_is_false_rw

interactive not_equal {| intro[AutoMustComplete] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H>; 'a = 'b in int >- "false" } -->
   sequent { <H> >- 'a <> 'b }

interactive elim_nequal {| elim |} 'H :
   sequent { <H>; <J[it]> >- "assert"{beq_int{'a; 'b}} } -->
   sequent { <H>; x: 'a <> 'b; <J['x]> >- 'C['x] }

interactive not_nequal :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- not{'a <> 'b} } -->
   sequent { <H> >- 'a = 'b in int }

let notNequalT = not_nequal

interactive le_refl {| intro []; nth_hyp |} :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- le{'a;'a} }

interactive ge_refl {| intro []; nth_hyp |} :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- ge{'a;'a} }

interactive ge_sqstable {| squash; intro []; nth_hyp |} :
   sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- it in ('a >= 'b) }

interactive lt_sqstable {| squash; intro []; nth_hyp |} :
   sequent { <H> >- 'a < 'b } -->
   sequent { <H> >- it in ('a < 'b) }

interactive ne_sqstable {| squash; intro []; nth_hyp |} :
   sequent { <H> >- 'a <> 'b } -->
   sequent { <H> >- it in ('a <> 'b) }

doc <:doc<
   The following rules establish decidability of integer relations and
   improve the @hreftactic[decideT] tactic.
>>

interactive ge_decidable {| intro [] |} :
   [wf] sequent{ <H> >- 'a in int } -->
   [wf] sequent{ <H> >- 'b in int } -->
   sequent{ <H> >- decidable{('a >= 'b)} }

interactive ge_addWeakMono {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- ('a +@ 'c) >= ('b +@ 'c) }

interactive ge_addWeakMono2 {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- ('c +@ 'a) >= ('c +@ 'b) }

interactive ge_Transit 'b :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- 'b >= 'c } -->
   sequent { <H> >- 'a >= 'c }

interactive ge_addMono :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   [wf] sequent { <H> >- 'd in int } -->
   sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- 'c >= 'd } -->
   sequent { <H> >- ('a +@ 'c) >= ('b +@ 'd) }

interactive_rw ge_to_left_rw :
	('a in int) -->
	('b in int) -->
	('a >= 'b) <--> ('a -@ 'b >= 0)

let ge_to_leftC = ge_to_left_rw

interactive_rw lt_bool2le_bool_rw :
	('a in int) -->
	('b in int) -->
	('a <@ 'b) <--> (('a +@ 1)<=@'b)

let lt_bool2le_boolC = lt_bool2le_bool_rw

let le_bool2lt_boolC = foldC <<'a <@ 'b>> lt_bool2le_boolC

doc <:doc<
   @modsubsection{A more convenient induction rule}
>>
interactive intElimination2 'H :
   [downcase] sequent { <H>; n: int; <J['n]>; m: int; 'm <= 0; 'C['m] >- 'C['m -@ 1] } -->
   [basecase] sequent { <H>; n: int; <J['n]> >- 'C[0] } -->
   [upcase] sequent { <H>; n: int; <J['n]>; m: int; 'm >= 0; 'C['m] >- 'C['m +@ 1] } -->
   sequent { <H>; n: int; <J['n]> >- 'C['n] }

interactive_rw guarded_ind_down 'x :
   ('x in int) -->
   ('x <= 0) -->
   ind{'x -@ 1; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
    ('down['x -@ 1; ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

interactive_rw guarded_ind_up 'x :
   ('x in int) -->
   ('x >= 0) -->
   ind{'x +@ 1; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
   ('up['x +@ 1; ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

doc docoff

let mkGuardT conv =
   let auxT = argfunT (fun i p ->
      if is_equal_term (concl p) then equalityAxiom (i-1) else hypothesis i)
   in funT (fun p ->
      let hyps = hyp_count p in
      let v = nth_binding p (hyps - 2) in
      let x = mk_var_term v in
         rwh (conv x) 0 thenAT auxT (hyps - 1))

let indDownT = mkGuardT guarded_ind_down
let indUpT = mkGuardT guarded_ind_up

let resource elim +=
   <<int>>, wrap_elim (fun i -> (intElimination2 i thenT thinIfThinningT [i]) thenLT [indDownT; rwh reduce_ind_base 0; indUpT])

interactive min_wf {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- min{'a; 'b} in int }

interactive max_wf {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- max{'a; 'b} in int }

interactive max_self1 {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- max{'a; 'b} >= 'a }

interactive max_self2 {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- max{'a; 'b} >= 'b }

interactive min_self1 {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- 'a >= min{'a; 'b} }

interactive min_self2 {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- 'b >= min{'a; 'b} }

interactive min_add {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- min{'a; 'b} +@'c = min{'a +@ 'c; 'b +@ 'c} in int }

interactive max_add {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- max{'a; 'b} +@'c = max{'a +@ 'c; 'b +@ 'c} in int }

interactive max_commut {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- max{'a; 'b} = max{'b; 'a} in int }

interactive max_reduce1 {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- max{'b; 'a} = 'a in int }

interactive max_reduce2 {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- max{'a; 'b} = 'a in int }

interactive min_commut {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- min{'a; 'b} = min{'b; 'a} in int }

interactive min_reduce1 {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- min{'b; 'a} = 'b in int }

interactive min_reduce2 {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- min{'a; 'b} = 'b in int }

interactive_rw min_reduce {| reduce |} :
   'a in int -->
   min{'a; 'a} <--> 'a

interactive_rw max_reduce {| reduce |} :
   'a in int -->
   max{'a; 'a} <--> 'a

interactive max_ge_left {| intro [SelectOption 0] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'x in int } -->
   sequent { <H> >- 'a >= 'x } -->
   sequent { <H> >- max{'a; 'b} >= 'x }

interactive max_ge_right {| intro [SelectOption 1] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'x in int } -->
   sequent { <H> >- 'b >= 'x } -->
   sequent { <H> >- max{'a; 'b} >= 'x }

interactive max_le {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'x in int } -->
   sequent { <H> >- 'x >= 'a } -->
   sequent { <H> >- 'x >= 'b } -->
   sequent { <H> >- 'x >=  max{'a; 'b} }

interactive min_ge_left {| intro [SelectOption 0] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'x in int } -->
   sequent { <H> >- 'x >= 'a } -->
   sequent { <H> >- 'x >= min{'a; 'b} }

interactive min_ge_right {| intro [SelectOption 1] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'x in int } -->
   sequent { <H> >- 'x >= 'b } -->
   sequent { <H> >- 'x >= min{'a; 'b} }

interactive min_le {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'x in int } -->
   sequent { <H> >- 'a >= 'x } -->
   sequent { <H> >- 'b >= 'x } -->
   sequent { <H> >- min{'a; 'b} >= 'x }

doc <:doc<
   @modsection{Well-formedness and algebraic properties of <<('x) *@ ('x)>>}
>>

interactive mul_wf {| intro [complete_unless_member] |} :
   [wf] sequent { <H> >- 'a = 'a1 in int } -->
   [wf] sequent { <H> >- 'b = 'b1 in int } -->
   sequent { <H> >- 'a *@ 'b = 'a1 *@ 'b1 in int }

interactive mul_add_Distrib :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ('a *@ ('b +@ 'c)) ~ (('a *@ 'b) +@ ('a *@ 'c)) }

interactive_rw mul_add_Distrib_rw {| arith_unfold |} :
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   ('a *@ ('b +@ 'c)) <--> (('a *@ 'b) +@ ('a *@ 'c))

let mul_add_DistribC = mul_add_Distrib_rw

interactive mul_Id {| intro []; nth_hyp |} :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- (1 *@ 'a) ~ 'a }

interactive_rw mul_Id_rw {| reduce; arith_unfold |} :
   'a in int -->
   (1 *@ 'a) <--> 'a

let mul_IdC = mul_Id_rw

interactive mul_Id2 {| nth_hyp |} :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- ('a *@ 1) ~ 'a }

interactive_rw mul_Id2_rw {| reduce; arith_unfold |} :
   ('a in int) -->
   ('a *@ 1) <--> 'a

let mul_Id2C = mul_Id2_rw

interactive mul_Id3 {| nth_hyp |} :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- 'a ~ (1 *@ 'a) }

interactive_rw mul_Id3_rw ('a :> Term) :
   ('a in int) -->
   'a <--> (1 *@ 'a)

let mul_Id3C = termC mul_Id3_rw

interactive mul_Zero {| intro[] |} :
   sequent { <H> >- (0 *@ 'a) ~ 0 }

interactive_rw mul_Zero_rw {| reduce; arith_unfold |} :
   (0 *@ 'a) <--> 0

let mul_ZeroC = mul_Zero_rw

interactive mul_Zero2 {| nth_hyp |} :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- ('a *@ 0) ~ 0 }

interactive_rw mul_Zero2_rw {| reduce; arith_unfold |} :
   ('a in int) -->
   ('a *@ 0) <--> 0

let mul_Zero2C = mul_Zero2_rw

interactive_rw mul_Zero3C 'a :
   0 <--> (0 *@ 'a)

interactive_rw negative1_2uniC {| reduce |} :
	('a in int) -->
	((-1) *@ 'a) <--> (- 'a)

interactive_rw negative1_2uni2C {| reduce |} :
	'a in int -->
	'a *@ (-1) <--> (- 'a)

interactive_rw uni2negative1C :
	('a in int) -->
	(- 'a) <--> ((-1) *@ 'a)

interactive mul_Commut :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a *@ 'b) ~ ('b *@ 'a) }

interactive_rw mul_Commut_rw :
   ('a in int) -->
   ('b in int) -->
   ('a *@ 'b) <--> ('b *@ 'a)

let mul_CommutC = mul_Commut_rw

interactive_rw mul_add_Distrib2C :
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   (('a *@ 'b) +@ ('a *@ 'c)) <--> ('a *@ ('b +@ 'c))

interactive_rw mul_add_Distrib3C {| arith_unfold |} :
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   (('a +@ 'b) *@ 'c) <--> (('a *@ 'c) +@ ('b *@ 'c))

interactive_rw minus_mul_assoc_rw {| reduce |} :
   'a in int -->
   'b in int -->
   ((-'a) *@ 'b) <--> - ('a *@ 'b)

interactive mul_Assoc :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ('a *@ ('b *@ 'c)) ~ (('a *@ 'b) *@ 'c) }

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

doc docoff

let resource reduce +=
   << ('a *@ 'b) *@ 'c>>, wrap_reduce_crw (addrC [Subterm 1] reduceC thenC addrC [Subterm 2] reduceC thenC tryC mul_Assoc2_rw)

let resource arith_unfold +=
	<<- 'a>>, uni2negative1C

doc docon

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

interactive_rw mul_uni_Assoc_rw {| reduce |} :
   ('a in int) -->
   ('b in int) -->
   ('a *@ (- 'b)) <--> ((- 'a) *@ 'b)

let mul_uni_AssocC = mul_uni_Assoc_rw

interactive_rw lt_reverse_rw :
	('a in int) -->
	('b in int) -->
	lt_bool{'a ; 'b} <--> lt_bool{(-'b) ; (- 'a)}

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

interactive beq_mulMono :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	[wf] sequent { <H> >- 'c in int } -->
	sequent { <H> >- 'c <> 0 } -->
	sequent { <H> >- beq_int{'a;'b} = beq_int{'c *@ 'a; 'c *@ 'b} in bool }

interactive beq_mulMonoSq :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	[wf] sequent { <H> >- 'c in int } -->
	sequent { <H> >- 'c <> 0 } -->
	sequent { <H> >- beq_int{'a;'b} ~ beq_int{'c *@ 'a; 'c *@ 'b} }

interactive_rw beq_mulMono_rw 'c :
	('a in int ) -->
	('b in int ) -->
	('c in int ) -->
	('c <> 0 ) -->
	beq_int{'a;'b} <--> beq_int{'c *@ 'a; 'c *@ 'b}

doc <:doc<
   @modsection{Definition and well-formedness of <<'x %@ 'x>>}
>>
prim rem_baseReduce :
   sequent { <H> >- 'a >= 0 } -->
   sequent { <H> >- 'a < 'b } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a %@ 'b) ~ 'a } = it

interactive_rw rem_baseReduce_rw :
   ('a >= 0) -->
   ('a < 'b) -->
   ('a in int) -->
   ('b in int) -->
   ('a %@ 'b) <--> 'a

let rem_baseReduceC = rem_baseReduce_rw

prim rem_neg :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a %@ 'b) ~ ('a %@ (-'b)) } = it

interactive_rw rem_neg_rw :
   ('b <> 0) -->
   ('a in int) -->
   ('b in int) -->
   ('a %@ 'b) <--> ('a %@ (-'b))

let rem_negC = rem_neg_rw

prim rem_indReduce :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ((('a *@ 'b) +@ 'c) %@ 'b) ~ ('c %@ 'b) } = it

interactive_rw rem_indReduce_rw :
   ('b <> 0) -->
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   ((('a *@ 'b) +@ 'c) %@ 'b) <--> ('c %@ 'b)

let rem_indReduceC = rem_indReduce_rw

interactive rem_wf {| intro [] |} :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a %@ 'b) in int }

doc <:doc<
   @modsection{Definition and properties of <<'x /@ 'x>>}
>>
prim div_baseReduce :
   sequent { <H> >- 'a >= 0 } -->
   sequent { <H> >- 'a < 'b } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a /@ 'b) ~ 0 } = it

interactive_rw div_baseReduce_rw :
   ('a >= 0) -->
   ('a < 'b) -->
   ('a in int) -->
   ('b in int) -->
   ('a /@ 'b) <--> 0

let div_baseReduceC = div_baseReduce_rw

prim div_neg :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a /@ 'b) ~ ((-'a) /@ (-'b)) } = it

interactive_rw div_neg_rw :
   ('b <> 0) -->
   ('a in int) -->
   ('b in int) -->
   ('a /@ 'b) <--> ((-'a) /@ (-'b))

let div_negC = div_neg_rw

prim div_indReduce :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ((('a *@ 'b) +@ 'c) /@ 'b) ~ ('a +@ ('c /@ 'b)) } = it

interactive_rw div_indReduce_rw :
   ('b <> 0) -->
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   ((('a *@ 'b) +@ 'c) /@ 'b) <--> ('a +@ ('c /@ 'b))

let div_indReduceC = div_indReduce_rw

interactive div_wf {| intro [] |} :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- 'a /@ 'b in int }

interactive div_remProperty :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
	sequent { <H> >- ('a %@ 'b) +@ ('a /@ 'b) *@ 'b = 'a in int }

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
   sequent { <H> >- 'a >= 0 } -->
   sequent { <H> >- 0 < 'b } -->
   sequent { <H> >- 0 < 'c } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- (('a /@ 'b) /@ 'c) ~ ('a /@ ('b *@ 'c)) }

interactive_rw div_Assoc_rw :
   ('a >= 0) -->
   (0 < 'b) -->
   (0 < 'c) -->
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   (('a /@ 'b) /@ 'c) <--> ('a /@ ('b *@ 'c))

let div_AssocC = div_Assoc_rw

doc <:doc<
   @modsection{Integer segmentation properties}
>>
interactive intSegUniv {| intro [] |} :
   sequent { <H> >- 'a in int} -->
   sequent { <H> >- 'b in int} -->
   sequent { <H> >- int_seg{'a; 'b} in univ[i:l] }

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
   sequent { <H>; x: int; v:'x >= 'i; w: 'x < 'j; <J['x]> >- 'C['x] }  -->
   sequent { <H>; x: int_seg{'i; 'j}; <J['x]> >- 'C['x] }

interactive intSegIsInt {| nth_hyp |} 'H :
   sequent { <H>; x: int_seg{'i; 'j}; <J['x]> >- 'x in int }

doc docoff

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
