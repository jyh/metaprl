doc <:doc<
   @module[Itt_list3]

   This is another library of list operations.

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2005-2006 Mojave Group, Caltech

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

   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
   @end[license]

   @parents
>>
extends Itt_bool
extends Itt_dfun
extends Itt_image
extends Itt_list2
extends Itt_list3
extends Itt_nat
extends Itt_pairwise

doc docoff

open Basic_tactics
open Itt_struct
open Itt_equal

(*
 * Some arithmetic helper rules.
 *)
interactive one_eq_nat_plus_two_elim {| elim [] |} 'H :
   [wf] sequent { <H>; x: (1 = 'j +@ 2 in nat); <J['x]> >- 'j in nat } -->
   sequent { <H>; x: (1 = 'j +@ 2 in nat); <J['x]> >- 'C['x] }

interactive nat_plus_one_eq_nat_plus_two_intro {| intro [] |} :
   [wf] sequent { <H> >- 'j in nat } -->
   [wf] sequent { <H> >- 'k in nat } -->
   sequent { <H> >- 'j = 'k +@ 1 in nat } -->
   sequent { <H> >- 'j +@ 1 = 'k +@ 2 in nat }

doc <:doc<
   Define a relaxed form of list type.  The type << Nil >> includes
   just << nil >>.  The type << Cons >> includes all cons-cells
   << cons{'e1; 'e2} >> for any << 'e1 >> and << 'e2 >>.
>>
define unfold_Nil : Nil <-->
   Img{unit; x. nil}

define unfold_Cons : Cons <-->
   Img{top * top; x. spread{'x; u, v. cons{'u; 'v}}}

define unfold_cons_of_fun : cons_of_fun{'x} <-->
   spread{'x; n, f. ind{'n; 'f 0; i, g. ('f 'i) :: 'g}}

define unfold_ConsNInfo : ConsInfo{'n} <-->
   { i: nat | 'i = 'n in nat } * (nat -> top)

define unfold_ConsN : Cons{'n} <-->
   Img{ConsInfo{'n}; x. cons_of_fun{'x}}

doc <:doc<
   These are types.
>>
interactive nil_wf {| intro [] |} :
   sequent { <H> >- Nil Type }

interactive cons_wf {| intro [] |} :
   sequent { <H> >- Cons Type }

interactive cons_n_info_wf {| intro [] |} :
   [wf] sequent { <H> >- 'n in nat } -->
   sequent { <H> >- ConsInfo{'n} Type }

interactive cons_n_wf {| intro [] |} :
   [wf] sequent { <H> >- 'n in nat } -->
   sequent { <H> >- Cons{'n} Type }

doc <:doc<
   Introduction and elimination rules.
>>
interactive nil_intro {| intro [] |} :
   sequent { <H> >- nil in Nil }

interactive nil_elim {| elim [ThinOption thinT] |} 'H :
   sequent { <H>; x: Nil; <J[nil]> >- 'C[nil] } -->
   sequent { <H>; x: Nil; <J['x]> >- 'C['x] }

interactive cons_intro {| intro [] |} :
   sequent { <H> >- cons{'e1; 'e2} in Cons }

interactive cons_elim {| elim [] |} 'H :
   sequent { <H>; u: top; v: top; <J[cons{'u; 'v}]> >- 'C[cons{'u; 'v}] } -->
   sequent { <H>; x: Cons; <J['x]> >- 'C['x] }

doc <:doc<
   The @tt[list_elim] lemma is extremely useful for splitting lists.
   It is elimination only, not an induction principle.
>>
interactive list_elim 'H :
   [base] sequent { <H>; <J[nil]> >- 'C[nil] } -->
   [step] sequent { <H>; u: top; v: list; <J[cons{'u; 'v}]> >- 'C[cons{'u; 'v}] } -->
   sequent { <H>; x: list; <J['x]> >- 'C['x] }

doc docoff

interactive cons_elim_member 'H :
   sequent { <H>; x: ('y in Cons); <J['x]>; 'y ~ cons{hd{'y}; tl{'y}} >- 'C['x] } -->
   sequent { <H>; x: ('y in Cons); <J['x]> >- 'C['x] }

interactive cons_n_intro 'n :
   [wf] sequent { <H> >- 'n in nat } -->
   [wf] sequent { <H> >- 'n > 0 } -->
   [wf] sequent { <H> >- 'e in Cons{'n} } -->
   sequent { <H> >- 'e in Cons }

(*
 * Lemmas for parts.
 *)
interactive cons_n_info_intro {| intro [] |} :
   [wf] sequent { <H> >- 'i = 'j in nat } -->
   [wf] sequent { <H> >- 'f in nat -> top } -->
   sequent { <H> >- ('i, 'f) in ConsInfo{'j} }

interactive cons_of_fun_intro {| intro [] |} :
   [wf] sequent { <H> >- 'i in nat } -->
   [wf] sequent { <H> >- 'f in nat -> top } -->
   sequent { <H> >- cons_of_fun{('i, 'f)} in Cons{'i} }

(*
 * Reductions.
 *)
interactive_rw reduce_cons_of_fun_zero {| reduce |} :
   cons_of_fun{(0, 'f)}
   <-->
   'f 0

interactive_rw reduce_cons_of_fun_succ {| reduce |} :
   'i in nat -->
   cons_of_fun{('i +@ 1, 'f)}
   <-->
   'f ('i +@ 1) :: cons_of_fun{('i, 'f)}

(*
 * Membership judgments.
 *)
interactive cons_n_intro_nil {| intro [] |} :
   sequent { <H> >- 'e in Cons{0} }

interactive tl_cons_intro {| intro [] |} :
   [wf] sequent { <H> >- 'n in nat } -->
   [wf] sequent { <H> >- 'e in Cons{'n +@ 1} } -->
   sequent { <H> >- tl{'e} in Cons{'n} }

(************************************************************************
 * Lemmas for the introduction rule.
 *)
define unfold_fun_of_cons : fun_of_cons{'n; 'l} <-->
   lambda{i. if beq_int{'i; 0} then nth_suffix{'l; 'n} else nth{'l; 'n -@ 'i}}

interactive fun_of_cons_wf {| intro [] |} :
   sequent { <H> >- fun_of_cons{'i; 'x} in nat -> top }

interactive_rw reduce_fun_of_cons_zero {| reduce |} :
   fun_of_cons{'n; 'l} 0
   <-->
   nth_suffix{'l; 'n}

interactive_rw reduce_fun_of_cons_succ {| reduce |} :
   'i in nat -->
   fun_of_cons{'n; 'l} ('i +@ 1)
   <-->
   nth{'l; 'n -@ ('i +@ 1)}

interactive cons_of_fun_eq {| intro [] |} :
   [wf] sequent { <H> >- 'f1 in nat -> top } -->
   [wf] sequent { <H> >- 'f2 in nat -> top } -->
   sequent { <H> >- 'm in nat } -->
   sequent { <H>; i: nat; 'i <= 'm >- 'f1 'i ~ 'f2 'i } -->
   sequent { <H> >- cons_of_fun{('m, 'f1)} ~ cons_of_fun{('m, 'f2)} }

interactive_rw reduce_cons_of_fun_of_cons {| reduce |} :
   'm in nat -->
   'l in Cons{'m} -->
   cons_of_fun{('m, fun_of_cons{'m; 'l})}
   <-->
   'l

doc <:doc<
   These are the main introduction and elimination lemmmas for the sloppy lists.
>>
interactive cons_n_elim {| elim [] |} 'H :
   [wf] sequent { <H>; x: Cons{'n}; <J['x]> >- 'n in nat } -->
   [wf] sequent { <H>; x: Cons{'n}; <J['x]> >- 'n > 0 } -->
   sequent { <H>; u: top; v: Cons{'n -@ 1}; <J[cons{'u; 'v}]> >- 'C[cons{'u; 'v}] } -->
   sequent { <H>; x: Cons{'n}; <J['x]> >- 'C['x] }

interactive cons_n_intro_cons {| intro [] |} :
   [wf] sequent { <H> >- 'n in nat } -->
   [wf] sequent { <H> >- 'n > 0 } -->
   [wf] sequent { <H> >- 'e2 IN Cons{'n -@ 1} } -->
   sequent { <H> >- cons{'e1; 'e2} in Cons{'n} }

(************************************************************************
 * Now define a function space for functions that produce conses.
 *)
doc <:doc<
   Define a space of lambdas that compute to cons lists.
>>
define unfold_ConsFun : ConsFun <-->
   Img{(top -> top) * (top -> top); x. spread{'x; u, v. lambda{y. cons{'u 'y; 'v 'y}}}}

define unfold_cons_of_fun_arg : cons_of_fun_arg{'x} <-->
   spread{'x; n, f. lambda{y. cons_of_fun{('n, 'f 'y)}}}

define unfold_ConsNFunInfo : ConsFunInfo{'n} <-->
   { i: nat | 'i = 'n in nat } * (top -> nat -> top)

define unfold_ConsNFun : ConsFun{'n} <-->
   Img{ConsFunInfo{'n}; x. cons_of_fun_arg{'x}}

doc docoff

(*
 * Bleh, workaround for bugs in hypSubstT.
 *)
define unfold_guard : guard{'e} <--> 'e

let fold_guard = makeFoldC << guard{'e} >> unfold_guard

(*
 * Rewrites.
 *)
interactive_rw reduce_cons_of_fun_arg_pair {| reduce |} :
   cons_of_fun_arg{('n, 'f)}
   <-->
   lambda{y. cons_of_fun{('n, 'f 'y)}}

(*
 * Simple form.
 *)
interactive cons_fun_wf {| intro [] |} :
   sequent { <H> >- ConsFun Type }

interactive cons_fun_cons_wf {| intro [] |} :
   sequent { <H> >- lambda{x. cons{'e1['x]; 'e2['x]}} in ConsFun }

interactive_rw cons_fun_split hd{'x} :
   'x in ConsFun -->
   'x
   <-->
   lambda{y. hd{'x 'y}::tl{'x 'y}}

interactive cons_fun_elim_member 'H :
   sequent { <H>; x: ('y in ConsFun); <J['x]>; 'y ~ lambda{z. cons{hd{'y 'z}; tl{'y 'z}}} >- 'C['x] } -->
   sequent { <H>; x: ('y in ConsFun); <J['x]> >- 'C['x] }

(*
 * Well-formedness.
 *)
interactive cons_n_fun_info_wf {| intro [] |} :
   [wf] sequent { <H> >- 'n in nat } -->
   sequent { <H> >- ConsFunInfo{'n} Type }

interactive cons_n_fun_pair_in_info {| intro [] |} :
   [wf] sequent { <H> >- 'n = 'm in nat } -->
   [wf] sequent { <H> >- 'f in top -> nat -> top } -->
   sequent { <H> >- ('n, 'f) in ConsFunInfo{'m} }

interactive cons_n_fun_wf {| intro [] |} :
   [wf] sequent { <H> >- 'n in nat } -->
   sequent { <H> >- ConsFun{'n} Type }

interactive cons_of_fun_in_cons_fun {| intro [] |} :
   [wf] sequent { <H> >- 'n = 'm in nat } -->
   [wf] sequent { <H> >- 'f in top -> nat -> top } -->
   sequent { <H> >- cons_of_fun_arg{('n, 'f)} in ConsFun{'m} }

interactive cons_n_fun_intro 'n :
   [wf] sequent { <H> >- 'n in nat } -->
   [wf] sequent { <H> >- 'n > 0 } -->
   [wf] sequent { <H> >- 'f in ConsFun{'n} } -->
   sequent { <H> >- 'f in ConsFun }

(*
 * Tail membership.
 *)
interactive cons_fun_intro_nil {| intro [] |} :
   sequent { <H> >- lambda{x. 'e['x]} in ConsFun{0} }

interactive tl_cons_fun_intro {| intro [] |} :
   [wf] sequent { <H> >- 'n in nat } -->
   [wf] sequent { <H> >- 'f in ConsFun{'n +@ 1} } -->
   sequent { <H> >- lambda{x. tl{'f 'x}} in ConsFun{'n} }

(*
 * Flatten theorems.
 *)
interactive cons_lambda_eq {| intro [] |} :
   sequent { <H> >- lambda{x. 'e1['x]} ~ lambda{x. 'e3['x]} } -->
   sequent { <H> >- lambda{x. 'e2['x]} ~ lambda{x. 'e4['x]} } -->
   sequent { <H> >- lambda{x. 'e1['x] :: 'e2['x]} ~ lambda{x. 'e3['x] :: 'e4['x]} }

interactive cons_of_fun_lambda_eq {| intro [] |} :
   [wf] sequent { <H> >- 'f1 in top -> nat -> top } -->
   [wf] sequent { <H> >- 'f2 in top -> nat -> top } -->
   sequent { <H> >- 'm in nat } -->
   sequent { <H>; i: nat; 'i <= 'm >- lambda{x. 'f1 'x 'i} ~ lambda{x. 'f2 'x 'i} } -->
   sequent { <H> >- lambda{x. cons_of_fun{('m, 'f1 'x)}} ~ lambda{x. cons_of_fun{('m, 'f2 'x)}} }

interactive cons_n_fun_flatten :
   sequent { <H> >- 'n in nat } -->
   sequent { <H> >- 'f in ConsFun{'n} } -->
   sequent { <H> >- lambda{x. cons_of_fun{('n, fun_of_cons{'n; 'f 'x})}} ~ lambda{x. 'f 'x} }

interactive_rw reduce_cons_n_fun_flatten :
   'n in nat -->
   lambda{x. 'e['x]} in ConsFun{'n} -->
   lambda{x. cons_of_fun{('n, fun_of_cons{'n; 'e['x]})}}
   <-->
   lambda{x. 'e['x]}

doc <:doc<
   Introduction and elimination rules.
>>
interactive cons_n_fun_elim_cons {| elim [] |} 'H :
   [wf] sequent { <H>; x: ConsFun{'n}; <J['x]> >- 'n in nat } -->
   [wf] sequent { <H>; x: ConsFun{'n}; <J['x]> >- 'n > 0 } -->
   sequent { <H>; u: top -> top; v: ConsFun{'n -@ 1}; <J[lambda{x. cons{'u 'x; 'v 'x}}]> >-
      'C[lambda{x. cons{'u 'x; 'v 'x}}] } -->
   sequent { <H>; x: ConsFun{'n}; <J['x]> >- 'C['x] }

interactive cons_n_fun_intro_cons {| intro [] |} :
   [wf] sequent { <H> >- 'n in nat } -->
   [wf] sequent { <H> >- 'n > 0 } -->
   [wf] sequent { <H> >- lambda{x. 'e2['x]} in ConsFun{'n -@ 1} } -->
   sequent { <H> >- lambda{x. cons{'e1['x]; 'e2['x]}} in ConsFun{'n} }

(************************************************************************
 * Squiggle equality.
 *)
doc <:doc<
   One of the reasons to define sloppy lists is to allow general lemmas
   about squiggle equality of lists.  The general form splits the list using
   the << nth_prefix{'l; 'i} >> and << nth_suffix{'l; 'i} >> terms.
>>
interactive split_list 'i 'n :
   [wf] sequent { <H> >- 'n in nat } -->
   [wf] sequent { <H> >- 'l in Cons{'n} } -->
   [wf] sequent { <H> >- 'i in nat } -->
   [wf] sequent { <H> >- 'i < 'n } -->
   sequent { <H> >- 'l ~ append{nth_prefix{'l; 'i}; nth_suffix{'l; 'i}} }

interactive_rw split_list_sqequal 'i ('l :> Term) :
   'l in list -->
   'i in nat -->
   'i <= length{'l} -->
   'l
   <-->
   append{nth_prefix{'l; 'i}; nth_suffix{'l; 'i}}

doc <:doc<
   This is a key equality lemma.  Two lists are equal if they are split
   at an arbitrary point, and the prefixes and suffixes are equal.
>>
interactive split_list_pair 'i 'n :
   [wf] sequent { <H> >- 'n in nat } -->
   [wf] sequent { <H> >- 'l1 in Cons{'n} } -->
   [wf] sequent { <H> >- 'l2 in Cons{'n} } -->
   [wf] sequent { <H> >- 'i in nat } -->
   [wf] sequent { <H> >- 'i < 'n } -->
   sequent { <H> >- append{nth_prefix{'l1; 'i}; nth_suffix{'l1; 'i}} ~ append{nth_prefix{'l2; 'i}; nth_suffix{'l2; 'i}} } -->
   sequent { <H> >- 'l1 ~ 'l2 }

(************************************************************************
 * Induction lemmas.
 *)
interactive_rw reduce_last_suffix {| reduce |} :
   'n in nat -->
   'e in Cons{'n} -->
   nth_suffix{nth_prefix{'e; 'n}; 'n}
   <-->
   nil

(************************************************************************
 * Tactics.
 *)
doc docoff

let cons_type_term = << Cons >>
let cons_fun_type_term = << ConsFun >>

(*
 * Given an expression in Cons, add the split equation.
 *)
let splitConsT t =
   let t_mem = mk_equal_term cons_type_term t t in
      assertT t_mem
      thenLT [idT; cons_elim_member (-1) thenT thinT (-2)]

let splitConsFunT t =
   let t_mem = mk_equal_term cons_fun_type_term t t in
      assertT t_mem
      thenLT [idT; cons_fun_elim_member (-1) thenT thinT (-2)]

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
