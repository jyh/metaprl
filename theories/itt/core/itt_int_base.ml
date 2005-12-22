doc <:doc<
   @module[Itt_int_base]

   The integers are formalized as a @emph{primitive}
   type in the @Nuprl type theory. This module defines additive fragment
   (<<'x +@ 'y>>, <<'x -@ 'y>>, <<- 'x>>)
   with linear order both in propositional (<<'x < 'y>>)
   and boolean (<<lt_bool{'x ; 'y}>>) forms.
	It was decided that because inequalities on integers are decidable, it would
   be better to define boolean inequalities as primitive ones and
   propositional as derived (via <<"assert"{'x}>>) from the correspondent
   boolean inequalities.

   The theory of integers continues in @hrefmodule[Itt_int_ext] where multiplicative
   operations and other inequality relations are added.
   @hrefmodule[Itt_int_arith] adds @hrefconv[normalizeC], that is capable of
   converting polynomials to their canonical forms, and @hreftactic[arithT], that
   is capable of proving simple integer inequalities.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998-2005 MetaPRL Group, Cornell University, Moscow State
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

doc <:doc<
   @parents
>>
extends Itt_equal
extends Itt_squash
extends Itt_dfun
extends Itt_bool
extends Itt_logic
extends Itt_struct
extends Itt_struct2
extends Itt_decidable
extends Itt_sqsimple
doc docoff

open Lm_debug
open Lm_printf

open Basic_tactics
open Base_meta

open Itt_equal
open Itt_struct
open Itt_squash
open Itt_bool
open Itt_squiggle
open Itt_sqsimple

let _ = show_loading "Loading Itt_int_base%t"

let debug_arith_unfold =
   create_debug (**)
      { debug_name = "arith_unfold";
        debug_description = "display Itt_int_base.arith_unfold steps";
        debug_value = false
      }

(*
 * RESOURCES USED BY arithT
 *)
let extract_data tbl =
   let rw e =
      let t = env_term e in
      let conv =
         try
            (* Find and apply the right tactic *)
            if !debug_arith_unfold then
               Lm_printf.eprintf "Conversionals: lookup %a%t" debug_print t eflush;
            Term_match_table.lookup tbl Term_match_table.select_all t
         with
            Not_found ->
               raise (RefineError ("Conversionals.extract_data", StringTermError ("no reduction for", t)))
      in
         if !debug_arith_unfold then
            Lm_printf.eprintf "Conversionals: applying %a%t" debug_print t eflush;
         conv
   in
      funC rw

let process_arith_unfold_resource_rw_annotation =
   redex_and_conv_of_rw_annotation "arith_unfold"

(*
 * Resource.
 *)
let resource (term * conv, conv) arith_unfold =
   Term_match_table.table_resource_info extract_data

let arith_unfoldTopC_env e =
   Sequent.get_resource_arg (env_arg e) get_arith_unfold_resource

let arith_unfoldTopC = funC arith_unfoldTopC_env

let arith_unfoldC =
   funC (fun e -> repeatC (lowerC (arith_unfoldTopC_env e)))

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @terms

   The @tt[int] term is the type of integers with elements
   $$@ldots, @number{-2}, @number{-1}, @number{0}, @number{1}, @number{2},
 @ldots$$
>>
declare int
declare number[n:n]
declare number{'a}

doc <:doc<
   The basic arithmetic operators are defined with
   the following terms. Basic predicates are boolean.
>>
declare "add"{'a; 'b}
declare minus{'a}

declare beq_int{'a; 'b}
declare lt_bool{'a; 'b}

doc <:doc<
   Subtraction is composition of addition and unary minus
>>
define unfold_sub :
   "sub"{'a ; 'b} <--> ('a +@ minus{'b})

let fold_sub = makeFoldC << 'a -@ 'b >> unfold_sub

doc <:doc<
   Derived propositional relation:

>>

define unfold_lt :
   lt{'a; 'b} <--> "assert"{lt_bool{'a; 'b}}

let fold_lt = makeFoldC << 'a < 'b >> unfold_lt

doc <:doc<
   The @tt[ind] term is the induction combinator for building
   loops indexed by an integer argument.
>>
declare ind{'i; m, z. 'down; 'base; m, z. 'up}

doc docoff

let int_term = << int >>
let int_opname = opname_of_term int_term
let is_int_term = is_no_subterms_term int_opname

let beq_int_term = << beq_int{'x; 'y} >>
let beq_int_opname = opname_of_term beq_int_term
let is_beq_int_term = is_dep0_dep0_term beq_int_opname
let mk_beq_int_term = mk_dep0_dep0_term beq_int_opname
let dest_beq_int = dest_dep0_dep0_term beq_int_opname

let lt_term = << 'x < 'y >>
let lt_opname = opname_of_term lt_term
let is_lt_term = is_dep0_dep0_term lt_opname
let mk_lt_term = mk_dep0_dep0_term lt_opname
let dest_lt = dest_dep0_dep0_term lt_opname

let lt_bool_term = << lt_bool{'x; 'y} >>
let lt_bool_opname = opname_of_term lt_bool_term
let is_lt_bool_term = is_dep0_dep0_term lt_bool_opname
let mk_lt_bool_term = mk_dep0_dep0_term lt_bool_opname
let dest_lt_bool = dest_dep0_dep0_term lt_bool_opname

let add_term = << 'x +@ 'y >>
let add_opname = opname_of_term add_term
let is_add_term = is_dep0_dep0_term add_opname
let mk_add_term = mk_dep0_dep0_term add_opname
let dest_add = dest_dep0_dep0_term add_opname

let minus_term = <<minus{'a}>>
let minus_opname = opname_of_term minus_term
let is_minus_term = is_dep0_term minus_opname
let mk_minus_term = mk_dep0_term minus_opname
let dest_minus = dest_dep0_term minus_opname

let sub_term = << 'x -@ 'y >>
let sub_opname = opname_of_term sub_term
let is_sub_term = is_dep0_dep0_term sub_opname
let mk_sub_term = mk_dep0_dep0_term sub_opname
let dest_sub = dest_dep0_dep0_term sub_opname

let number_term = << number[n:n] >>
let number_opname = opname_of_term number_term
let is_number_term = is_number_term number_opname
let dest_number = dest_number_term number_opname
let mk_number_term = mk_number_term number_opname

let ind_term = << ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} >>
let ind_opname = opname_of_term ind_term
let is_ind_term = is_dep0_dep2_dep0_dep2_term ind_opname
let dest_ind = dest_dep0_dep2_dep0_dep2_term ind_opname
let mk_ind_term = mk_dep0_dep2_dep0_dep2_term ind_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_compare
prec prec_add
prec prec_unary
prec prec_unary < prec_add

dform number_df : number[n:n] =
   slot[n:n]

dform beq_int_df1 : parens :: "prec"[prec_compare] :: beq_int{'a; 'b} =
   slot["lt"]{'a} `" =" Mpsymbols!subb `" " slot["le"]{'b}

dform add_df1 : except_mode[src] :: parens :: "prec"[prec_add] :: "add"{'a; 'b}
 =
   slot["le"]{'a} `" + " slot["lt"]{'b}
dform add_df2 : mode[src] :: parens :: "prec"[prec_add] :: "add"{'a; 'b} =
   slot["le"]{'a} `" +@ " slot["lt"]{'b}

dform minus_df1 : except_mode[src] :: parens :: "prec"[prec_unary] :: (- 'a) =
   `" - " slot["le"]{'a}
dform minus_df2 : mode[src] :: parens :: "prec"[prec_unary] :: (- 'a) =
   `" - " slot["le"]{'a}

dform sub_df1 : except_mode[src] :: parens :: "prec"[prec_add] :: "sub"{'a; 'b}
 =
   slot["lt"]{'a} `" - " slot["le"]{'b}
dform sub_df2 : mode[src] :: parens :: "prec"[prec_add] :: "sub"{'a; 'b} =
   slot["lt"]{'a} `" -@ " slot["le"]{'b}

dform lt_df1 : parens :: "prec"[prec_compare] :: lt{'a; 'b} =
   slot["lt"]{'a} `" < " slot["le"]{'b}

dform lt_bool_df1 : parens :: "prec"[prec_compare] :: lt_bool{'a; 'b} =
   slot["lt"]{'a} `" <" Mpsymbols!subb `" " slot["le"]{'b}

(*
 * XXX: JYH: this display form is rather poorly designed.
 * Why displya using the constant string "n" -- why
 * not use the binding variables that are present
 * in the original term.  Also, this display form substitutes
 * stuff into the expression bodies, which is not really
 * a good idea.
 *)
declare display_n : Dform
declare display_ind{'x : Dform } : Dform
declare display_ind_n : Dform
declare display_ind_eq{'x : Dform; 'y : Dform} : Dform

dform display_n_df : display_n =
   math_it["n":s]

dform display_ind_df1 : display_ind{'x} =
   math_it["Ind":s] `"(" 'x `")"

dform display_ind_df2 : display_ind_n =
   display_ind{display_n}

dform ind_eq_df: except_mode[src] :: display_ind_eq{'x;'y} =
   szone 'x space `"=" space 'y ezone

dform ind_df : parens :: "prec"[prec_bor] :: except_mode[src] ::
   ind{'x; i, j. 'down['i :> Dform; 'j :> Dform]; 'base; k, l. 'up['k :> Dform; 'l :> Dform]} =
   szone pushm[3]
     szone display_ind{'x} space `"where" space display_ind_n space `"=" ezone
   hspace
     math_implies{math_lt{display_n; 0}; display_ind_eq{display_ind_n; 'down[display_n; display_ind{math_add{display_n;1}}]}}
   hspace
     math_implies{display_ind_eq{display_n; 0}; display_ind_eq{display_ind_n; 'base}}
   hspace
     math_implies{math_lt{0; display_n}; display_ind_eq{display_ind_n; 'up[display_n; display_ind{math_sub{display_n;1}}]}}
   popm ezone

doc <:doc<
   @modsection{Rules and rewrites}
   @modsubsection{Operations and relations on literals}

   The binary arithmetic operators on literal integers are defined using the
   the @emph{meta} arithmetic operators that are @MetaPRL
   builtin operations.
>>
prim_rw reduce_numeral : number{meta_num[n:n]} <--> number[n:n]

prim_rw reduce_add_meta : (number[i:n] +@ number[j:n]) <-->
   number{meta_sum[i:n, j:n]}

prim_rw reduce_minus_meta : ( - number[i:n]) <-->
   number{meta_diff[0:n, i:n]}

prim_rw reduce_sub_meta : (number[i:n] -@ number[j:n]) <-->
   number{meta_diff[i:n, j:n]}

prim_rw reduce_lt_meta : lt_bool{number[i:n]; number[j:n]} <-->
   meta_lt[i:n, j:n]{btrue; bfalse}

prim_rw reduce_beq_int_meta : beq_int{number[i:n]; number[j:n]} <-->
   meta_eq[i:n, j:n]{btrue; bfalse}

doc docoff

let reduce_add =
   reduce_add_meta thenC (addrC [Subterm 1] reduce_meta_sum) thenC reduce_numeral

let reduce_minus =
   reduce_minus_meta thenC (addrC [Subterm 1] reduce_meta_diff) thenC reduce_numeral

let reduce_sub =
   reduce_sub_meta thenC (addrC [Subterm 1] reduce_meta_diff) thenC reduce_numeral

let reduce_lt =
   reduce_lt_meta thenC reduce_meta_lt_num

let reduce_eq_int =
   reduce_beq_int_meta thenC reduce_meta_eq_num

let resource arith_unfold += [
   <<number[i:n] +@ number[j:n]>>, reduce_add;
   <<minus{number[i:n]}>>, reduce_minus;
   <<number[i:n] -@ number[j:n]>>, reduce_sub;
]

let resource reduce += [
   <<number[i:n] +@ number[j:n]>>, reduce_add;
   <<minus{number[i:n]}>>, reduce_minus;
   <<number[i:n] -@ number[j:n]>>, reduce_sub;
   <<lt_bool{number[i:n]; number[j:n]}>>, reduce_lt;
   <<number[i:n] < number[j:n]>>, (unfold_lt thenC addrC [Subterm 1] reduce_lt);
   <<beq_int{number[i:n]; number[j:n]}>>, reduce_eq_int;
]

(*
 * Useful tactic to prove _rw from ~-rules
 *)
let sqFromRwT t =
   (funT (fun p -> sqSubstT (Sequent.concl p) 0))
   thenMT
      autoT
   thenT t thenT trivialT

doc <:doc<
   @modsubsection{Integers are canonical}
>>

prim int_sqequal {| nth_hyp |} :
   sequent { <H> >- 'a = 'b in int } -->
   sequent { <H> >- 'a ~ 'b } = it

interactive_rw int_sqequal_rw ('a ~ 'b) :
   ('a = 'b in int) -->
   'a <--> 'b

let int_sqequalC = int_sqequal_rw

doc <:doc<
   @modsubsection{Typehood and well-formedness of @tt[int] and @tt[number]}

   The $@int$ type inhabits every universe, and it
   is a type.
>>
(*
 * H >- Z = Z in Ui ext Ax
 * by intEquality
 *)
prim intEquality {| intro [] |} :
   sequent { <H> >- int in univ[i:l] } = it

(*
 * H >- int Type
 *)
interactive intType {| intro [] |} :
   sequent { <H> >- "type"{int} }

(*
 * Int is a sqsimple type.
 *)
interactive int_sqsimple {| intro []; sqsimple |} :
   sequent { <H> >- sqsimple{int} }

(*
 * H >- Ui ext Z
 * by intFormation
 *)
interactive intFormation :
   sequent { <H> >- univ[i:l] }

(*
 * H >- Z ext n
 * by numberFormation n
 *)
prim numberFormation {| intro [] |} number[n:n] :
   sequent { <H> >- int } = number[n:n]

let resource intro += (<<int>>, wrap_intro (numberFormation <<0>>))

doc <:doc<
   @modsubsection{Well-formedness of operations and relations}

>>

prim add_wf {| intro [complete_unless_member] |} :
   [wf] sequent { <H> >- 'a = 'a1 in int } -->
   [wf] sequent { <H> >- 'b = 'b1 in int } -->
   sequent { <H> >- 'a +@ 'b = 'a1 +@ 'b1 in int } = it

prim minus_wf {| intro [] |} :
   [wf] sequent { <H> >- 'a = 'a1 in int } -->
   sequent { <H> >- (-'a) = (-'a1) in int } = it

interactive sub_wf {| intro [complete_unless_member] |} :
   [wf] sequent { <H> >- 'a = 'a1 in int } -->
   [wf] sequent { <H> >- 'b = 'b1 in int } -->
   sequent { <H> >- 'a -@ 'b = 'a1 -@ 'b1 in int }

prim lt_bool_wf {| intro [complete_unless_member] |} :
   sequent { <H> >- 'a='a1 in int } -->
   sequent { <H> >- 'b='b1 in int } -->
   sequent { <H> >- lt_bool{'a; 'b} = lt_bool{'a1; 'b1} in bool } = it

prim beq_wf {| intro [complete_unless_member] |} :
   [wf] sequent { <H> >- 'a = 'a1 in int } -->
   [wf] sequent { <H> >- 'b = 'b1 in int } -->
   sequent { <H> >- beq_int{'a; 'b} = beq_int{'a1; 'b1} in bool } = it

interactive lt_squashStable {| squash |} :
   sequent { <H> >- 'a < 'b } -->
   sequent { <H> >- it in ('a < 'b) }

interactive lt_wf {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- "type"{lt{'a; 'b}} }

interactive lt_univ {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- lt{'a; 'b} in univ[i:l] }

doc <:doc<
   @modsubsection{Correspondence between <<beq_int{'a;'b}>> and <<'a='b in int>> }

>>
prim beq_int2prop :
   [main] sequent { <H> >- "assert"{beq_int{'a; 'b}} } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- 'a = 'b in int } = it

(* Derived from previous *)
interactive eq_int_assert_elim {| elim [ThinOption thinT] |} 'H :
   [main]sequent{ <H>; x:"assert"{beq_int{'a;'b}}; <J[it]>;
                            y: 'a = 'b in int >- 'C[it]} -->
   [wf]sequent{ <H>; x:"assert"{beq_int{'a;'b}}; <J[it]> >- 'a in int} -->
   [wf]sequent{ <H>; x:"assert"{beq_int{'a;'b}}; <J[it]> >- 'b in int} -->
   sequent{ <H>; x:"assert"{beq_int{'a;'b}}; <J['x]> >- 'C['x]}

prim beq_int_is_true {| nth_hyp |} :
   sequent { <H> >- 'a = 'b in int } -->
   sequent { <H> >- beq_int{'a; 'b} ~ btrue } = it

interactive_rw beq_int_is_true_rw :
   ('a = 'b in int) -->
   beq_int{'a; 'b} <--> btrue

let beq_int_is_trueC = beq_int_is_true_rw

(*
 Derived from previous rewrite
 *)
interactive eq_2beq_int {| intro []; nth_hyp |} :
   sequent { <H> >- 'a = 'b in int } -->
   sequent { <H> >- "assert"{beq_int{'a; 'b}} }

interactive lt_bool_member {| intro []; nth_hyp |} :
  [main]  sequent { <H> >- 'a < 'b } -->
(*  [wf] sequent { <H> >- 'a in int } -->
  [wf] sequent { <H> >- 'b in int } --> *)
  sequent { <H> >- "assert"{lt_bool{'a; 'b}} }

doc <:doc<
   @modsubsection{Decidability}
   The following rules establish decidability of integer relations and
   improve the @hreftactic[decideT] tactic.
>>
interactive lt_decidable {| intro [] |} :
   [wf] sequent{ <H> >- 'a in int } -->
   [wf] sequent{ <H> >- 'b in int } -->
   sequent{ <H> >- decidable{('a < 'b)} }

interactive eq_int_decidable {| intro [] |} :
   [wf] sequent{ <H> >- 'a in int } -->
   [wf] sequent{ <H> >- 'b in int } -->
   sequent{ <H> >- decidable{('a = 'b in int)} }

doc <:doc<
   @modsubsection{Membership}

   The $@int$ type contains the @hrefterm[number] terms.
>>
(*
 * H >- i = i in int
 * by numberEquality
 *)
prim numberEquality {| intro [] |} :
   sequent { <H> >- number[n:n] in int } = it

doc <:doc<
   @modsubsection{Order relation properties}

   <<lt_bool{'a;'b}>> defines irreflexive, asymmetric, transitive and
   discrete order on @tt[int]
>>

prim lt_Reflex :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- band{lt_bool{'a; 'b}; lt_bool{'b; 'a}} ~ bfalse } =
 it

interactive_rw lt_Reflex_rw {| reduce |} :
   ( 'a in int ) -->
   ( 'b in int ) -->
   band{lt_bool{'a; 'b}; lt_bool{'b; 'a}} <--> bfalse

let lt_ReflexC = lt_Reflex_rw

interactive_rw lt_irreflex_rw {| reduce |} :
   ( 'a in int ) -->
   lt_bool{'a;'a} <--> bfalse

let lt_IrreflexC = lt_irreflex_rw

interactive irrefl_Elimination 'H 'J :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	sequent { <H>; x: 'a < 'b; <J['x]>; y: 'b < 'a; <K['x;'y]> >- 'C['x;'y] }

let irrefl_EliminationT i j = funT (fun p ->
   let i = get_pos_hyp_num p i in
   let j = get_pos_hyp_num p j in
      irrefl_Elimination i (j-i))

interactive irreflElim {| elim [] |} 'H :
	[wf] sequent { <H> >- 'a in int } -->
	sequent { <H>; x: 'a < 'a; <J['x]> >- 'C['x] }

interactive lt_Asym 'a 'b :
   [main] sequent { <H> >- 'a < 'b } -->
   [main] sequent { <H> >- 'b < 'a } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- 'C }

let lt_AsymT = lt_Asym

prim lt_Trichot :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent {
     <H> >- bor{bor{lt_bool{'a; 'b};lt_bool{'b; 'a}}; beq_int{'a; 'b}} ~ btrue
 } = it

interactive_rw lt_Trichot_rw :
   ( 'a in int ) -->
   ( 'b in int ) -->
   bor{bor{lt_bool{'a; 'b};lt_bool{'b; 'a}}; beq_int{'a; 'b}} <--> btrue

let lt_TrichotC = lt_Trichot_rw

let splitIntC a b =
   foldC
      (mk_bor_term
         (mk_bor_term
            (mk_lt_bool_term a b)
            (mk_lt_bool_term b a))
         (mk_beq_int_term a b))
      lt_TrichotC

interactive splitInt 'a 'b :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [main] sequent { <H>; w: ('a < 'b) >- 'C } -->
   [main] sequent { <H>; w: 'a = 'b in int >- 'C } -->
   [main] sequent { <H>; w: ('b < 'a) >- 'C } -->
   sequent { <H> >- 'C }

doc <:doc<
   @begin[description]
   @item{@tactic[splitIntT];
    { The @tt[splitIntT] <<'a>> <<'b>> tactic uses @tt[splitInt] rule to split
      reasoning into three cases - when <<'a>> is less then, equal to or
      greater then <<'b>>.}}
   @end[description]
   @docoff
>>

let splitIntT = splitInt

prim lt_Transit 'b :
   [main] sequent {
      <H> >- band{lt_bool{'a; 'b};lt_bool{'b; 'c}} = btrue in bool } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- lt_bool{'a; 'c} ~ btrue } = it

interactive_rw lt_Transit_rw 'b :
   band{lt_bool{'a; 'b};lt_bool{'b; 'c}} = btrue in bool -->
   ( 'a in int ) -->
   ( 'b in int ) -->
   ( 'c in int ) -->
   lt_bool{'a; 'c} <--> btrue

let lt_TransitC = lt_Transit_rw

interactive ltDissect 'b:
   [main] sequent { <H> >- 'a < 'b } -->
   [main] sequent { <H> >- 'b < 'c } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- 'a < 'c }

let ltDissectT = ltDissect

prim lt_Discret :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- lt_bool{'a; 'b} ~
                          bor{beq_int{('a +@ 1); 'b}; lt_bool{('a +@ 1); 'b}} }
 = it

interactive_rw lt_Discret_rw :
   ( 'a in int ) -->
   ( 'b in int ) -->
   lt_bool{'a; 'b} <--> bor{beq_int{('a +@ 1); 'b}; lt_bool{('a +@ 1); 'b}}

let lt_DiscretC = lt_Discret_rw

doc <:doc<
   @modsubsection{Elimination}

   Induction on an integer assumption produces three cases:
   one for the base case $0$, one for induction on negative arguments,
   and another for induction on positive arguments.  The proof extract term
   uses the @tt[ind] term, which performs a case analysis on its argument.
>>
(*
 * Induction:
 * H, n:Z, J[n] >- C[n] ext ind(i; m, z. down[n, m, it, z]; base[n]; m, z.
up[n, m, it, z])
 * by intElimination [m; v; z]
 *
 * H, n:Z, J[n], m:Z, v: m < 0, z: C[m + 1] >- C[m] ext down[n, m, v, z]
 * H, n:Z, J[n] >- C[0] ext base[n]
 * H, n:Z, J[n], m:Z, v: 0 < m, z: C[m - 1] >- C[m] ext up[n, m, v, z]
 *)
prim intEliminationLast :
      ( 'down['m; 'v; 'z] : sequent { <H>; m: int; v: 'm < 0; z: 'C['m +@ 1] >- 'C['m] } ) -->
      ( 'base : sequent { <H> >- 'C[0] } ) -->
      ( 'up['m; 'v; 'z] : sequent { <H>; m: int; v: 0 < 'm; z: 'C['m -@ 1] >- 'C['m] } ) -->
      sequent { <H>; n: int >- 'C['n] } = ind{'n; m, z. 'down['m; it; 'z]; 'base; m,z. 'up['m; it; 'z]}

interactive intElimination {| elim [ThinOption thinT] |} 'H :
   [downcase] sequent { <H>; n: int; <J['n]>; m: int; 'm < 0; 'C['m +@ 1] >- 'C['m] } -->
   [basecase] sequent { <H>; n: int; <J['n]> >- 'C[0] } -->
   [upcase] sequent { <H>; n: int; <J['n]>; m: int; 0 < 'm; 'C['m -@ 1] >- 'C['m] } -->
   sequent { <H>; n: int; <J['n]> >- 'C['n] }

doc <:doc<
   @modsubsection {Induction and recursion}
   Reduction of the induction combinator @tt[ind] has three cases.
   If the argument $x$ is $0$, the combinator reduces to the @i{base}
   case; if it is positive, it reduces to the @i{up} case; and
   if it is negative, it reduces to the @i{down} case.
   The first argument in the @i{up} and @i{down} cases represents
   the induction value, and the second argument represents the
   ``next'' computational step.
>>
(*
 * Reduction on induction combinator:
 * Three cases:
 *    let ind[x] = ind(x; i, j. down[i, j]; base; k, l. up[k, l]
 *    x < 0 => (ind[x] -> down[x, ind[x + 1]]
 *    x = 0 => (ind[x] -> base)
 *    x > 0 => (ind[x] -> up[x, ind[x - 1]]
 *)
prim_rw reduce_ind_down :
   ('x < 0) -->
   ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
    ('down['x; ind{('x +@ 1); i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

prim_rw reduce_ind_up :
   (0 < 'x) -->
   ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
   ('up['x; ind{('x -@ 1); i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

prim_rw reduce_ind_base :
   (ind{0; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}) <-->
   'base

interactive_rw unfold_ind :
   ('i in int) -->
   ind{'i; m, z. 'down['m;'z]; 'base; m, z. 'up['m;'z]} <-->
      (if beq_int{'i; 0} then 'base else
         if lt_bool{0;'i}
         then 'up['i; ind{('i -@ 1); m, z. 'down['m; 'z]; 'base; m, z. 'up['m;
 'z]}]
         else 'down['i; ind{('i +@ 1); m, z. 'down['m; 'z]; 'base; m,z. 'up['m;
 'z]}])

interactive_rw unfold_ind_number :
   ind{number[n:n]; m, z. 'down['m;'z]; 'base; m, z. 'up['m;'z]} <-->
      (if beq_int{number[n:n]; 0} then 'base else
         if lt_bool{0;number[n:n]}
         then 'up[number[n:n]; ind{(number[n:n] -@ 1); m, z. 'down['m; 'z];
 'base; m, z. 'up['m; 'z]}]
         else 'down[number[n:n]; ind{(number[n:n] +@ 1); m, z. 'down['m; 'z];
 'base; m,z. 'up['m; 'z]}])

let reduce_ind_numberC =
   unfold_ind_number thenC addrC [Subterm 3; Subterm 1] reduce_lt thenC addrC [Subterm 3] reduceTopC
 thenC addrC [Subterm 1] reduce_eq_int thenC reduceTopC

doc <:doc<
   @modsubsection{Addition properties}

   @tt[add] is commutative and associative.

>>
prim add_Commut :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a +@ 'b) ~ ('b +@ 'a) } = it

interactive_rw add_Commut_rw :
   ( 'a in int ) -->
   ( 'b in int ) -->
   ('a +@ 'b) <--> ('b +@ 'a)

let add_CommutC = add_Commut_rw

prim add_Assoc :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ('a +@ ('b +@ 'c)) ~ (('a +@ 'b) +@ 'c) } = it

interactive_rw add_Assoc_rw :
   ( 'a in int ) -->
   ( 'b in int ) -->
   ( 'c in int ) -->
   ('a +@ ('b +@ 'c)) <--> (('a +@ 'b) +@ 'c)

let add_AssocC = add_Assoc_rw

interactive_rw add_Assoc2_rw {| reduce |} :
   ( 'a in int ) -->
   ( 'b in int ) -->
   ( 'c in int ) -->
   (('a +@ 'b) +@ 'c) <--> ('a +@ ('b +@ 'c))

let add_Assoc2C = add_Assoc2_rw

doc <:doc<

   0 is neutral element for @tt[add] in @tt[int]

>>
prim add_Id {| nth_hyp |} :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- ('a +@ 0) ~ 'a } = it

interactive_rw add_Id_rw {| reduce; arith_unfold |} :
   ( 'a in int ) -->
   ('a +@ 0) <--> 'a

let add_IdC = add_Id_rw

interactive_rw add_Id2_rw {| reduce; arith_unfold |} :
   ( 'a in int ) -->
   (0 +@ 'a) <--> 'a

let add_Id2C = add_Id2_rw

let resource reduce += [
	<<'a -@ 0>>, (unfold_sub thenC (addrC [Subterm 2] reduce_minus));
]

interactive_rw add_Id3_rw ('a :> Term) :
   ( 'a in int ) -->
   'a <--> (0 +@ 'a)

let add_Id3C = termC add_Id3_rw

interactive_rw add_Id4_rw ('a :> Term) :
   ( 'a in int ) -->
   'a <--> ('a +@ 0)

let add_Id4C = termC add_Id4_rw

doc <:doc<

   Monotonicity:

>>
prim lt_addMono :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- lt_bool{('a +@ 'c); ('b +@ 'c)} ~ lt_bool{'a; 'b} } =
 it

interactive_rw lt_bool_addMono_rw {| reduce |} :
   ( 'a in int ) -->
   ( 'b in int ) -->
   ( 'c in int ) -->
   lt_bool{('a +@ 'c); ('b +@ 'c)} <--> lt_bool{'a; 'b}

interactive_rw lt_addMono_rw1 {| reduce |} :
   ( 'a in int ) -->
   ( 'b in int ) -->
   ( 'c in int ) -->
   (('a +@ 'c) < ('b +@ 'c)) <--> ('a < 'b)

interactive_rw lt_addMono_rw2 {| reduce |} :
   ( 'a in int ) -->
   ( 'b in int ) -->
   ( 'c in int ) -->
   (('a +@ 'b) < ('a +@ 'c)) <--> ('b < 'c)

interactive_rw lt_addMono_rw 'c:
   ( 'a in int ) -->
   ( 'b in int ) -->
   ( 'c in int ) -->
   ('a < 'b) <--> (('a +@ 'c) < ('b +@ 'c))

interactive_rw lt_const {| reduce |} :
   ( 'a in int ) -->
   ( 'b in int ) -->
   ( 'a < ('a +@ 'b) ) <--> ( 0 < 'b)

interactive lt_add_lt :
   [main] sequent { <H> >- 'a < 'b} -->
   [main] sequent { <H> >- 'c < 'd} -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   [wf] sequent { <H> >- 'd in int } -->
   sequent { <H> >- ('a +@ 'c) < ('b +@ 'd) }

doc docoff

let lt_addMonoC = lt_addMono_rw
let lt_add_ltT = lt_add_lt

doc <:doc<

   <<- 'a>> is an inverse element for <<'a>> in <<int>>

>>
prim minus_add_inverse {| nth_hyp |} :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- ( 'a +@ (- 'a ) ) ~ 0 } = it

interactive_rw minus_add_inverse_rw {| reduce |} :
   ( 'a in int ) -->
   ( 'a +@ (- 'a) ) <--> 0

let minus_add_inverseC = minus_add_inverse_rw

interactive add_Functionality 'c :
   [main] sequent { <H> >- ('a +@ 'c) ~ ('b +@ 'c) } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- 'a ~ 'b }

interactive_rw add_Functionality_rw 'b 'c ('a :> Term) :
   (('a +@ 'c) ~ ('b +@ 'c)) -->
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   'a <--> 'b

let add_FunctionalityC b c =
   termC (add_Functionality_rw b c)

interactive minus_minus_reduce {| nth_hyp |} :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- (-(-'a)) ~ 'a }

interactive_rw minus_minus_reduce_rw {| reduce |} :
   ('a in int) -->
   (-(-'a)) <--> 'a

let minus_minus_reduceC = minus_minus_reduce_rw

interactive_rw minus_same_rw {| reduce |} :
   ('a in int) -->
   ('a -@ 'a) <--> 0
   
interactive_rw minus_same_rw2 {| reduce |} :
   ('a in int) -->
   (- 'a) +@ 'a <--> 0

interactive_rw plus_minus_rw {| reduce |} :
   ('a in int) -->
   ('b in int) -->
   (('a +@ 'b) -@ 'b) <--> 'a

interactive_rw minus_plus_rw {| reduce |} :
   ('a in int) -->
   ('b in int) -->
   (('a -@ 'b) +@ 'b) <--> 'a

interactive minus_add_Distrib {| intro [] |} :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- (-('a +@ 'b)) ~ ((-'a) +@ (-'b)) }

interactive_rw minus_add_Distrib_rw :
   'a in int -->
   'b in int -->
    (-('a +@ 'b)) <--> ((-'a) +@ (-'b))

let minusDistribC = minus_add_Distrib_rw

(*
 * @modsubsection{Combinator equality}
 *
 * Two @tt[ind] term compute values of type $T$ if each of the three
 * cases (zero, positive, and negative) produces values of type $T$.
 *)
(*
 * Equality on induction combinator:
 * let a = ind(x1; i1, j1. down1[i1, j1]; base1; k1, l1. up1[k1, l1])
 * let b = ind(x2; i2, j2. down2[i2, j2]; base2; k2, l2. up2[k2, l2])
 *
 * H >- a = b in T[x1]
 * by indEquality \z. T[z]
 *
 * H >- x1 = y1 in Z
 * H, x: Z, w: x < 0, y: T[x + 1] >- down1[x, y] = down2[x, y] in T[x]
 * H >- base1 = base2 in T[0]
 * H, x: Z, w: 0 < x, y: T[x - 1] >- up1[x, y] = up2[x, y] in T[x]
 *)
interactive indEquality {| intro [complete_unless_member] |} bind{z. 'T['z]} :
   [wf] sequent { <H> >- 'x1 = 'x2 in int } -->
   [downcase] sequent { <H>; x: int; 'x < 0; 'x1 < 'x +@ 1; y: 'T['x +@ 1] >- 'down1['x; 'y] =
 'down2['x; 'y] in 'T['x] } -->
   [basecase] sequent { <H> >- 'base1 = 'base2 in 'T[0] } -->
   [upcase] sequent { <H>; x: int; 0 < 'x; 'x < 'x1 +@ 1; y: 'T['x -@ 1] >- 'up1['x; 'y] =
 'up2['x; 'y] in 'T['x] } -->
   sequent { <H> >- ind{'x1; i1, j1. 'down1['i1; 'j1]; 'base1; k1, l1.
 'up1['k1; 'l1]}
                   = ind{'x2; i2, j2. 'down2['i2; 'j2]; 'base2; k2, l2.
 'up2['k2; 'l2]}
                   in 'T['x1] }

doc docoff

(***********************************************************
 * TYPE INFERENCE
 ***********************************************************)

(*
 * Type of int and of number
 *)
let resource typeinf += [
   (<<int>>, infer_univ1);
   (<<number[n:n]>>, Typeinf.infer_const <<int>>)
]

let resource reduce += [
   << ('a < 'a) >>, (unfold_lt thenC (addrC [Subterm 1] lt_irreflex_rw));
   <<ind{number[n:n]; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}>>, reduce_ind_numberC;
]

doc docoff
