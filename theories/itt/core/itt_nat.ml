doc <:doc<
   @module[Itt_nat]

   Theory of natural numbers.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2001 Alexei Kopylov, Cornell University

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

   Author: Alexei Kopylov @email{kopylov@cs.cornell.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_equal
extends Itt_dfun
extends Itt_logic
extends Itt_bool
extends Itt_struct3
extends Itt_int_base
extends Itt_int_ext
extends Itt_int_arith
extends Itt_sqsimple
doc docoff

open Basic_tactics

open Itt_struct
open Itt_equal
open Itt_bool
open Itt_subtype
open Itt_int_arith
open Itt_sqsimple

doc terms

define unfold_nat : nat <--> ({x:int | 'x>=0})
define unfold_finite_nat : nat{'k} <--> int_seg{0; 'k}

let fold_finite_nat = makeFoldC << nat{'k} >> unfold_finite_nat

define unfold_nat_plus : nat_plus <--> ({x:int | 'x>0})

define unfoldInd : ind{'n; 'base; k,l. 'up['k;'l]} <-->
                   ind{'n; i,j.it; 'base; k,l . 'up['k;'l]}

define iform unfoldInd1 : ind{'n; 'base; l. 'up['l]} <-->
                    ind{'n; 'base; k,l . 'up['l]}

doc docoff

let foldInd = makeFoldC << ind{'n; 'base; k,l. 'up['k;'l]} >> unfoldInd

(******************
 *  Display Forms *
 ******************)

dform nat_prl_df : except_mode [src] :: nat = mathbbN
dform finite_nat_df1 : except_mode [src] :: nat{'k} = mathbbN sub{'k}
dform finite_nat_df2 : mode[src] :: nat{'k} = `"{0..(" slot{'k} `"-1)}"

dform nat_plus_df : except_mode[src] :: nat_plus = mathbbN sup{slot["*"]}

dform ind_df : parens :: "prec"[prec_bor] :: except_mode[src] ::
   ind{'x; 'base; k, l. 'up['k :> Dform; 'l :> Dform]} =
   szone pushm[3]
     szone display_ind{'x} space `"where" space display_ind_n space `"=" ezone
   hspace
     math_implies{display_ind_eq{display_n;0}; display_ind_eq{display_ind_n;'base}}
   hspace
     math_implies{math_gt{display_n; 0}; display_ind_eq{display_ind_n; 'up[display_n; display_ind{math_sub{display_n;1}}]}}
   popm ezone

doc rewrites

interactive_rw reduce_ind_up {| reduce |} :
   ('x in nat) -->
   ind{'x +@ 1; 'base; k,l. 'up['k;'l]} <-->
   ('up['x +@ 1; ind{'x ; 'base; k,l. 'up['k;'l]}])

interactive_rw reduce_ind_base {| reduce |} :
   (ind{0; 'base; k,l. 'up['k;'l]}) <-->
   'base

let reduce_ind_numberC =
   unfoldInd

let resource reduce += [
   <<ind{number[n:n]; 'base; k, l. 'up['k; 'l]}>>, reduce_ind_numberC;
]

let ind_term = << ind{'x; 'base; k, l. 'up['k; 'l]} >>
let ind_opname = opname_of_term ind_term
let is_ind_term = is_dep0_dep0_dep2_term ind_opname
let dest_ind = dest_dep0_dep0_dep2_term ind_opname
let mk_ind_term = mk_dep0_dep0_dep2_term ind_opname

doc rules

interactive natType {| intro [] |} :
   sequent { <H> >- "type"{nat} }

interactive natUniv {| intro [] |} :
   sequent { <H> >- nat in univ[i:l] }

interactive natMemberEquality {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'a='b in int} -->
   sequent { <H> >- 'a >= 0}  -->
   sequent { <H> >- 'a='b in nat}

interactive natMemberZero {| intro [] |} :
   sequent { <H> >- 0 in nat}

interactive nat_is_int {| nth_hyp |} :
   sequent { <H> >- 'a='b in nat} -->
   sequent { <H> >- 'a='b in int}

interactive nat_is_int2 {| nth_hyp |} 'H :
   sequent { <H>; a: nat; <J['a]> >- 'a in int }

interactive nat_is_subtype_of_int  {| intro[] |} :
   sequent { <H> >- nat subtype int }

interactive nat_sqsimple {| intro []; sqsimple |} :
   sequent { <H> >- sqsimple{nat} }

let resource sub += (RLSubtype ([<< nat >>, << int>>], nat_is_subtype_of_int  ))

interactive eq_nat_decidable {| intro [] |} :
   [wf] sequent{ <H> >- 'a in nat } -->
   [wf] sequent{ <H> >- 'b in nat } -->
   sequent{ <H> >- decidable{('a = 'b in nat)} }

interactive natElimination 'H :
   sequent { <H>; x: int; v:'x>=0; <J['x]> >- 'C['x]}  -->
   sequent { <H>; x: nat; <J['x]> >- 'C['x]}

interactive nat2ge {| ge_elim |} 'H :
   sequent { <H>; x: nat; <J['x]>; 'x>=0 >- 'C['x]}  -->
   sequent { <H>; x: nat; <J['x]> >- 'C['x]}

interactive ge2nat {| ge_intro |} :
   [wf] sequent { <H> >- 'n in int }  -->
   sequent { <H>; (-1) >= 'n >- "false" } -->
   sequent { <H> >- 'n in nat }

interactive ge_eq2nat {| ge_intro |} :
   [wf] sequent { <H> >- 'n in int }  -->
   [wf] sequent { <H> >- 'm in int }  -->
   sequent { <H>; 'n <> 'm >- "false" }  -->
   sequent { <H>; (-1) >= 'n; (-1) >= 'm >- "false" } -->
   sequent { <H> >- 'n = 'm in nat }

interactive nat_plusone {| nth_hyp |} 'H :
   sequent { <H>; a: nat; <J['a]> >- 'a +@ 1 in nat }

interactive nat_plus {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'a in nat } -->
   sequent { <H> >- 'b in nat } -->
   sequent { <H> >- ('a +@ 'b) in nat }

interactive natInduction {| elim [ThinOption thinT] |} 'H  :
   [base] sequent { <H>; n: nat; <J['n]> >- 'C[0] }  -->
   [step] sequent { <H>; n: nat; <J['n]>; m: nat;  'C['m] >- 'C['m +@ 1] }  -->
   sequent { <H>; n: nat; <J['n]> >- 'C['n] }

let thinNextLastT n = (thinT (-2) thenT thinT n)

interactive natInduction2 {| elim [ThinOption thinNextLastT] |} 'H  :
   [base] sequent { <H>; n: nat; <J['n]> >- 'C[0] }  -->
   [step] sequent { <H>; n: nat; <J['n]>; m: nat; 'm<'n; 'C['m] >- 'C['m +@ 1] }  -->
   sequent { <H>; n: nat; <J['n]> >- 'C['n] }

interactive natFullInduction (* {| elim [SelectOption 1; ThinOption thinT] |} *) 'H  :
   sequent { <H>; n: nat; <J['n]>; m: nat; all k: nat. (('k < 'm) => 'C['k]) >- 'C['m] }  -->
   sequent { <H>; n: nat; <J['n]> >- 'C['n] }

interactive natBasedFullInduction 'H bind{x.'f['x]} :
    [wf] sequent { <H>; x: 'T; <J['x]>; y : 'T >- 'f['y] in nat } -->
    sequent { <H>; x: 'T; <J['x]>; x1 : 'T; all x2 : 'T. (('f['x2] < 'f['x1]) => 'C['x2]) >- 'C['x1] } -->
    sequent { <H>; x: 'T; <J['x]> >- 'C['x] }

interactive natBackInduction 'n bind{x.'C['x]}  :
   [wf] sequent { <H> >- 'n in nat }  -->
   [base] sequent { <H> >- 'C['n] }  -->
   [step] sequent { <H>; m: nat;  z: 'C['m +@ 1] >- 'C['m] }  -->
   sequent { <H>  >- 'C[0] }

interactive indEquality {| intro [complete_unless_member] |} bind{z. 'T['z]} :
   [wf] sequent { <H> >- 'n1 = 'n2 in nat } -->
   [base] sequent { <H> >- 'base1 = 'base2 in 'T[0] } -->
   [step] sequent { <H>; x: nat; 0<'x; le{'x;'n1}; y: 'T['x -@ 1] >- 'up1['x; 'y] = 'up2['x; 'y] in 'T['x] } -->
   sequent { <H> >- ind{'n1; 'base1; k1, l1. 'up1['k1; 'l1]} = ind{'n2; 'base2; k2, l2. 'up2['k2; 'l2]} in 'T['n1] }

interactive finiteNatType {| intro [] |} :
   sequent { <H> >- 'k in int} -->
   sequent { <H> >- "type"{nat{'k}} }

interactive finiteNatUniv {| intro [] |} :
   sequent { <H> >- 'k in int} -->
   sequent { <H> >- nat{'k} in univ[i:l] }

interactive finiteNatMemberEquality {| intro [] |} :
   sequent { <H> >- 'a = 'b in int_seg{0; 'k} } -->
   sequent { <H> >- 'a = 'b in nat{'k} }

interactive finiteNatElimination {| elim [] |} 'H :
   sequent { <H>; x: int; v:'x >= 0; w: 'x < 'k; <J['x]> >- 'C['x] }  -->
   sequent { <H>; x: nat{'k}; <J['x]> >- 'C['x] }

interactive finiteNat_ge_elim {| ge_elim |} 'H :
	[wf] sequent { <H>; x: int; <J['x]> >- 'k in int } -->
   sequent { <H>; x: int; <J['x]>; 'x >= 0; 'k >= 'x+@1 >- 'C['x] }  -->
   sequent { <H>; x: nat{'k}; <J['x]> >- 'C['x] }

interactive finiteNat_ge_elim2 {| ge_elim |} 'H :
	[wf] sequent { <H>; t: 'x in nat{'k}; <J['t]> >- 'k in int } -->
   sequent { <H>; t: 'x in nat{'k}; <J['t]>; 'x >= 0; 'k >= 'x+@1 >- 'C['t] }  -->
   sequent { <H>; t: 'x in nat{'k}; <J['t]> >- 'C['t] }

interactive finiteNatIsInt {| nth_hyp |} 'H :
   sequent { <H>; x: nat{'k}; <J['x]> >- 'x in int }

interactive finiteNatIsNat {| nth_hyp |} 'H :
   sequent { <H>; x: nat{'k}; <J['x]> >- 'x in nat }

interactive finiteNatIsSmall {| nth_hyp |} 'H :
   sequent { <H>; x: nat{'k}; <J['x]> >- 'x < 'k }

interactive finiteNatIsInt2 {| nth_hyp |} 'H :
   sequent { <H>; t: 'x in nat{'k}; <J['t]> >- 'x in int }

interactive finiteNatIsNat2 {| nth_hyp |} 'H :
   sequent { <H>; t: 'x in nat{'k}; <J['t]> >- 'x in nat }

interactive finiteNatIsSmall2 {| nth_hyp |} 'H :
   sequent { <H>; t: 'x in nat{'k}; <J['t]> >- 'x < 'k }

doc docoff

let natBackInductionT =
   argfunT (fun n p -> natBackInduction n (get_bind_from_arg_or_concl_subst p <<0>>))

interactive max_nat_wf {| intro[AutoMustComplete] |} :
   [wf] sequent { <H> >- 'a in nat } -->
   [wf] sequent { <H> >- 'b in nat } -->
   sequent { <H> >- max{'a; 'b} in nat }

interactive min_nat_wf {| intro [] |} :
   [wf] sequent { <H> >- 'a in nat } -->
   [wf] sequent { <H> >- 'b in nat } -->
   sequent { <H> >- min{'a; 'b} in nat }

(*
 * Some applications
 *)

interactive int_div_rem {| intro [] |} :
   sequent { <H> >- 'm in int } -->
   sequent { <H> >- 'k in int } -->
   sequent { <H> >- 'k > 0 } -->
   sequent { <H> >- exst q: int. exst r: nat. (('m = 'k *@ 'q +@ 'r in int) & 'r < 'k) }

(*
 * If there is a positive number x such that P[x], then there is
 * a smallest positive number k such that P[k], as long as P[y]
 * is well-formed and decidable for any integer y.
 *)
interactive positive_rule1 {| intro [] |} :
   [wf] sequent { <H>; a: int >- "type"{'P['a]} } -->
   [wf] sequent { <H> >- 'n in int } -->
   [wf] sequent { <H> >- 'n > 0 } -->
   [decidable] sequent { <H>; a: int >- decidable{'P['a]} } -->
   sequent { <H> >- (all b: int. ('b > 0 & 'b <= 'n => not{'P['b]})) or (exst u: int. ('u > 0 & 'u <= 'n & 'P['u] & all b: int. (('b > 0 & 'P['b]) => 'b >= 'u))) }

let positiveRule1T = positive_rule1

interactive smallest_positive {| intro [] |} :
   [wf] sequent { <H>; a: int >- "type"{'P['a]} } -->
   [decidable] sequent { <H>; a: int >- decidable{'P['a]} } -->
   [main] sequent { <H> >- exst a: int. ('a > 0 & 'P['a]) } -->
   sequent { <H> >- exst u: int. ('u > 0 & 'P['u] & all b: int. (('b > 0 & 'P['b]) => 'b >= 'u)) }

let positiveRule2T = smallest_positive

(*interactive smallest_positive_elim {| elim [] |} 'H :
   sequent { <H>; x: exst a: int. ('a > 0 & 'P['a]); <J['x]>; y: exst u: int. ('u > 0 & 'P['u] & all b: int. (('b > 0 & 'P['b]) => 'b < 'u)) >- 'C['x] } -->
   sequent { <H>; x: exst a: int. ('a > 0 & 'P['a]); <J['x]> >- 'C['x] }
*)


(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
