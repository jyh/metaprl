doc <:doc<
   @spelling{int number ind add minus beq_int lt_bool}
  
   @begin[doc]
   @module[Itt_int_base]
  
   The integers are formalized as a @emph{primitive}
   type in the @Nuprl type theory.
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
doc <:doc< @docoff >>

open Printf
open Mp_debug
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Rformat
open Mp_resource

open Var
open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Top_conversionals

open Base_meta
open Base_auto_tactic
open Base_dtactic

open Itt_equal
open Itt_struct
open Itt_squash
open Itt_bool
open Itt_squiggle

let _ = show_loading "Loading Itt_int_base%t"
(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @terms
  
   The @tt{int} term is the type of integers with elements
   $$@ldots, @number{-2}, @number{-1}, @number{0}, @number{1}, @number{2},
 @ldots$$
   @end[doc]
>>
declare int
declare number[n:n]
declare number{'a}

doc <:doc< 
   @begin[doc]
   The basic arithmetic operators are defined with
   the following terms. Basic predicates are boolean.
   @end[doc]
>>
declare "add"{'a; 'b}
declare minus{'a}

declare beq_int{'a; 'b}
declare lt_bool{'a; 'b}

doc <:doc< 
   @begin[doc]
   Subtraction is composition of addition and unary minus
   @end[doc]
>>
define unfold_sub :
   "sub"{'a ; 'b} <--> ('a +@ minus{'b})

doc <:doc< 
   @begin[doc]
   The @tt{ind} term is the induction combinator for building
   loops indexed by an integer argument.
   @end[doc]
>>
declare ind{'i; m, z. 'down; 'base; m, z. 'up}

doc <:doc< 
   @begin[doc]
   Derived typed relations
  
   @end[doc]
>>
(*
 Prop-int-lt definition
 *)
define unfold_lt :
   lt{'a; 'b} <--> "assert"{lt_bool{'a; 'b}}
doc <:doc< @docoff >>

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

(*
prec prec_mul < prec_apply
prec prec_add < prec_mul
prec prec_compare < prec_add
*)

dform int_prl_df : except_mode [src] :: int = mathbbZ
dform int_src_df : mode[src] :: int = `"int"

dform number_df : number[n:n] =
   slot[n:n]

dform beq_int_df1 : parens :: "prec"[prec_compare] :: beq_int{'a; 'b} =
   slot["lt"]{'a} `" =" Nuprl_font!subb `" " slot["le"]{'b}

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
   slot["lt"]{'a} `" <" Nuprl_font!subb `" " slot["le"]{'b}

declare display_ind{'x}
declare display_ind_n
declare display_ind_eq{'x;'y}

dform display_ind_df1 : internal :: display_ind{'x} =
   display_var["Ind":v]{nil} `"(" 'x `")"

dform display_ind_df2 : internal :: display_ind_n =
   display_ind{display_var["n":v]{nil}}

dform ind_eq_df: internal :: except_mode[src] :: display_ind_eq{'x;'y} =
   szone 'x space `"=" space 'y ezone

dform ind_df : parens :: "prec"[prec_bor] :: except_mode[src] ::
   ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} =
   szone pushm[3] szone display_ind{'x} space `"where" space display_ind_n space
 `"=" ezone hspace
   ((display_var["n":v]{nil} < 0) => display_ind_eq{display_ind_n;
 'down[display_var["n":v]{nil}; display_ind{(display_var["n":v]{nil} +@ 1)}]})
 hspace
   (display_ind_eq{display_var["n":v]{nil};0} => display_ind_eq{display_ind_n;
 'base}) hspace
   ((0 < display_var["n":v]{nil}) => display_ind_eq{display_ind_n;
 'up[display_var["n":v]{nil}; display_ind{(display_var["n":v]{nil} -@ 1)}]})
 popm ezone

(*
 * Useful tactic to prove _rw from ~-rules
 *)
let sqFromRwT t =
   (fun p -> sqSubstT (Sequent.concl p) 0 p)
    thenMT
        autoT
    thenT t thenT trivialT

let testT p =
   let g =Sequent.goal p in
(*  let (g,_):(term * term list)=Refiner.Refiner.Refine.dest_msequent mseq in
   let es :
 Refiner.Refiner.TermMan.Term.esequent=Refiner.Refiner.TermMan.explode_sequent g
 in
   let (args,hyps,goals)=es in
   let gl = SEQ_SET.to_list goals in*)
   let h2=Refiner.Refiner.TermMan.nth_hyp g 2 in
   let s2=Refiner.Refiner.TermMan.nth_binding g 2 in
   begin
      print_term stdout g;
      printf "\nHL%sHL\n" s2;
      print_term stdout h2;
      print_term stdout (Refiner.Refiner.TermMan.nth_concl g 1);
(*      print_term_list stdout gl;*)
      failT p
   end

doc <:doc< 
   @begin[doc]
   @modsection{Rules and rewrites}
   @modsubsection{Typehood and well-formedness of arithmetic operators}
  
   @end[doc]
>>
(*
 * Integers are canonical.
 *)
prim int_sqequal :
   sequent [squash] { <H> >- 'a = 'b in int } -->
   sequent ['ext] { <H> >- 'a ~ 'b } = it

interactive_rw int_sqequal_rw 'b :
   ('a = 'b in int) -->
   'a <--> 'b

let int_sqequalC = int_sqequal_rw

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rewrites
  
   The binary arithmetic operators are defined using the
   the @emph{meta} arithmetic operators that are @MetaPRL
   builtin operations.
   @end[doc]
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
   reduce_add_meta thenC (addrC [0] reduce_meta_sum) thenC reduce_numeral

let reduce_minus =
   reduce_minus_meta thenC (addrC [0] reduce_meta_diff) thenC reduce_numeral

let reduce_sub =
   reduce_sub_meta thenC (addrC [0] reduce_meta_diff) thenC reduce_numeral

let reduce_lt =
   reduce_lt_meta thenC reduce_meta_lt_num

let reduce_eq_int =
   reduce_beq_int_meta thenC reduce_meta_eq_num

let resource reduce += [
   <<number[i:n] +@ number[j:n]>>, reduce_add;
   <<minus{number[i:n]}>>, reduce_minus;
   <<number[i:n] -@ number[j:n]>>, reduce_sub;
   <<lt_bool{number[i:n]; number[j:n]}>>, reduce_lt;
   <<number[i:n] < number[j:n]>>, (unfold_lt thenC addrC [0] reduce_lt);
   <<beq_int{number[i:n]; number[j:n]}>>, reduce_eq_int;
]

prim add_wf {| intro []; eqcd |} :
   [wf] sequent [squash] { <H> >- 'a = 'a1 in int } -->
   [wf] sequent [squash] { <H> >- 'b = 'b1 in int } -->
   sequent ['ext] { <H> >- 'a +@ 'b = 'a1 +@ 'b1 in int } = it

prim minus_wf {| intro []; eqcd |} :
   [wf] sequent [squash] { <H> >- 'a = 'a1 in int } -->
   sequent ['ext] { <H> >- (-'a) = (-'a1) in int } = it

interactive sub_wf {| intro []; eqcd |} :
   [wf] sequent [squash] { <H> >- 'a = 'a1 in int } -->
   [wf] sequent [squash] { <H> >- 'b = 'b1 in int } -->
   sequent ['ext] { <H> >- 'a -@ 'b = 'a1 -@ 'b1 in int }

prim lt_bool_wf {| intro []; eqcd |} :
   sequent [squash] { <H> >- 'a='a1 in int } -->
   sequent [squash] { <H> >- 'b='b1 in int } -->
   sequent ['ext] { <H> >- lt_bool{'a; 'b} = lt_bool{'a1; 'b1} in bool } = it

prim beq_wf {| intro []; eqcd |} :
   [wf] sequent [squash] { <H> >- 'a = 'a1 in int } -->
   [wf] sequent [squash] { <H> >- 'b = 'b1 in int } -->
   sequent ['ext] { <H> >- beq_int{'a; 'b} = beq_int{'a1; 'b1} in bool } = it
doc <:doc< @docoff >>

interactive lt_squashStable {| squash |} :
   sequent [squash] { <H> >- 'a < 'b } -->
   sequent ['ext] { <H> >- it in ('a < 'b) }

interactive lt_wf {| intro [] |} :
   [wf] sequent [squash] { <H> >- 'a in int } -->
   [wf] sequent [squash] { <H> >- 'b in int } -->
   sequent ['ext] { <H> >- "type"{lt{'a; 'b}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{@tt{beq_int} and @tt{= in int} correspondence}
  
   @end[doc]
>>
prim beq_int2prop :
   [main] sequent [squash] { <H> >- "assert"{beq_int{'a; 'b}} } -->
   [wf] sequent [squash] { <H> >- 'a in int } -->
   [wf] sequent [squash] { <H> >- 'b in int } -->
   sequent ['ext] { <H> >- 'a = 'b in int } = it

(* Derived from previous *)
interactive eq_int_assert_elim {| elim [ThinOption thinT] |} 'H :
   [main]sequent['ext]{ <H>; x:"assert"{beq_int{'a;'b}}; <J[it]>;
                            y: 'a = 'b in int >- 'C[it]} -->
   [wf]sequent['ext]{ <H>; x:"assert"{beq_int{'a;'b}}; <J[it]> >- 'a in int} -->
   [wf]sequent['ext]{ <H>; x:"assert"{beq_int{'a;'b}}; <J[it]> >- 'b in int} -->
   sequent['ext]{ <H>; x:"assert"{beq_int{'a;'b}}; <J['x]> >- 'C['x]}

prim beq_int_is_true :
   sequent [squash] { <H> >- 'a = 'b in int } -->
   sequent ['ext] { <H> >- beq_int{'a; 'b} ~ btrue } = it

interactive_rw beq_int_is_true_rw :
   ('a = 'b in int) -->
   beq_int{'a; 'b} <--> btrue

let beq_int_is_trueC = beq_int_is_true_rw

(*
 Derived from previous rewrite
 *)
interactive eq_2beq_int {| intro [] |} :
   sequent [squash] { <H> >- 'a = 'b in int } -->
   sequent ['ext] { <H> >- "assert"{beq_int{'a; 'b}} }

interactive lt_bool_member {| intro [] |} :
  [main]  sequent [squash] { <H> >- 'a < 'b } -->
(*  [wf] sequent [squash] { <H> >- 'a in int } -->
  [wf] sequent [squash] { <H> >- 'b in int } --> *)
  sequent ['ext] { <H> >- "assert"{lt_bool{'a; 'b}} }

doc <:doc< @docoff >>

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsubsection{Typehood and well-formedness of @tt{int} and @tt{number}}
  
   The $@int$ type inhabits every universe, and it
   is a type.
   @end[doc]
>>
(*
 * H >- Z = Z in Ui ext Ax
 * by intEquality
 *)
prim intEquality {| intro []; eqcd |} :
   sequent ['ext] { <H> >- int in univ[i:l] } = it

(*
 * H >- int Type
 *)
interactive intType {| intro [] |} :
   sequent ['ext] { <H> >- "type"{int} }
doc <:doc< @docoff >>

(*
 * H >- Ui ext Z
 * by intFormation
 *)
interactive intFormation :
   sequent ['ext] { <H> >- univ[i:l] }

(*
 * H >- Z ext n
 * by numberFormation n
 *)
prim numberFormation {| intro [] |} number[n:n] :
   sequent ['ext] { <H> >- int } = number[n:n]

doc <:doc< 
   @begin[doc]
   @modsubsection{Decidability}
   The following rules establish decidability of integer relations and
   improve the @hreftactic[decideT] tactic.
   @end[doc]
>>
interactive lt_decidable {| intro [] |} :
   [wf] sequent[squash] { <H> >- 'a in int } -->
   [wf] sequent[squash] { <H> >- 'b in int } -->
   sequent['ext] { <H> >- decidable{('a < 'b)} }

interactive eq_int_decidable {| intro [] |} :
   [wf] sequent[squash] { <H> >- 'a in int } -->
   [wf] sequent[squash] { <H> >- 'b in int } -->
   sequent['ext] { <H> >- decidable{('a = 'b in int)} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Membership}
  
   The $@int$ type contains the @hrefterm[number] terms.
   @end[doc]
>>
(*
 * H >- i = i in int
 * by numberEquality
 *)
prim numberEquality {| intro []; eqcd |} :
   sequent ['ext] { <H> >- number[n:n] in int } = it

doc <:doc< 
   @begin[doc]
   @modsubsection{Order relation properties}
  
   @tt{lt_bool} defines reflexive, decidable, transitive and
   discrete order on @tt{int}
   @end[doc]
>>
(*
 Definition of basic operations (and relations) on int
 *)

prim lt_Reflex :
   [wf] sequent [squash] { <H> >- 'a in int } -->
   [wf] sequent [squash] { <H> >- 'b in int } -->
   sequent ['ext] { <H> >- band{lt_bool{'a; 'b}; lt_bool{'b; 'a}} ~ bfalse } =
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

interactive lt_Asym 'a 'b :
   [main] sequent [squash] { <H> >- 'a < 'b } -->
   [main] sequent [squash] { <H> >- 'b < 'a } -->
   [wf] sequent [squash] { <H> >- 'a in int } -->
   [wf] sequent [squash] { <H> >- 'b in int } -->
   sequent ['ext] { <H> >- 'C }

let lt_AsymT = lt_Asym

prim lt_Trichot :
   [wf] sequent [squash] { <H> >- 'a in int } -->
   [wf] sequent [squash] { <H> >- 'b in int } -->
   sequent ['ext] {
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
   [wf] sequent [squash] { <H> >- 'a in int } -->
   [wf] sequent [squash] { <H> >- 'b in int } -->
   [main] sequent ['ext] { <H>; w: ('a < 'b) >- 'C } -->
   [main] sequent ['ext] { <H>; w: 'a = 'b in int >- 'C } -->
   [main] sequent ['ext] { <H>; w: ('b < 'a) >- 'C } -->
   sequent ['ext] { <H> >- 'C }

let splitIntT = splitInt

prim lt_Transit 'b :
   [main] sequent [squash] {
      <H> >- band{lt_bool{'a; 'b};lt_bool{'b; 'c}} = btrue in bool } -->
   [wf] sequent [squash] { <H> >- 'a in int } -->
   [wf] sequent [squash] { <H> >- 'b in int } -->
   [wf] sequent [squash] { <H> >- 'c in int } -->
   sequent ['ext] { <H> >- lt_bool{'a; 'c} ~ btrue } = it

interactive_rw lt_Transit_rw 'b :
   ( band{lt_bool{'a; 'b};lt_bool{'b; 'c}} = btrue in bool ) -->
   ( 'a in int ) -->
   ( 'b in int ) -->
   ( 'c in int ) -->
   lt_bool{'a; 'c} <--> btrue

let lt_TransitC = lt_Transit_rw

interactive ltDissect 'b:
   [main] sequent [squash] { <H> >- 'a < 'b } -->
   [main] sequent [squash] { <H> >- 'b < 'c } -->
   [wf] sequent [squash] { <H> >- 'a in int } -->
   [wf] sequent [squash] { <H> >- 'b in int } -->
   [wf] sequent [squash] { <H> >- 'c in int } -->
   sequent ['ext] { <H> >- 'a < 'c }

let ltDissectT = ltDissect

prim lt_Discret :
   [wf] sequent [squash] { <H> >- 'a in int } -->
   [wf] sequent [squash] { <H> >- 'b in int } -->
   sequent ['ext] { <H> >- lt_bool{'a; 'b} ~
                          bor{beq_int{('a +@ 1); 'b}; lt_bool{('a +@ 1); 'b}} }
 = it

interactive_rw lt_Discret_rw :
   ( 'a in int ) -->
   ( 'b in int ) -->
   lt_bool{'a; 'b} <--> bor{beq_int{('a +@ 1); 'b}; lt_bool{('a +@ 1); 'b}}

let lt_DiscretC = lt_Discret_rw

doc <:doc< 
   @begin[doc]
  
   Monotonicity:
  
   @end[doc]
>>
prim lt_addMono 'c :
   [wf] sequent [squash] { <H> >- 'a in int } -->
   [wf] sequent [squash] { <H> >- 'b in int } -->
   [wf] sequent [squash] { <H> >- 'c in int } -->
   sequent ['ext] { <H> >- lt_bool{'a; 'b} ~ lt_bool{('a +@ 'c); ('b +@ 'c)} } =
 it

interactive_rw lt_addMono_rw 'c :
   ( 'a in int ) -->
   ( 'b in int ) -->
   ( 'c in int ) -->
   lt_bool{'a; 'b} <--> lt_bool{('a +@ 'c); ('b +@ 'c)}

let lt_addMonoC = lt_addMono_rw

doc <:doc< 
   @begin[doc]
   @modsubsection{Elimination}
  
   Induction on an integer assumption produces three cases:
   one for the base case $0$, one for induction on negative arguments,
   and another for induction on positive arguments.  The proof extract term
   uses the @tt{ind} term, which performs a case analysis on its argument.
   @end[doc]
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
prim intElimination {| elim [ThinOption thinT] |} 'H :
   ( 'down['n; 'm; 'v; 'z] :
      sequent ['ext] { <H>; n: int; <J['n]>; m: int; v: 'm < 0; z: 'C['m +@ 1]
 >- 'C['m] } ) -->
   ( 'base['n] : sequent ['ext] { <H>; n: int; <J['n]> >- 'C[0] } ) -->
   ( 'up['n; 'm; 'v; 'z] : 
      sequent ['ext] { <H>; n: int; <J['n]>; m: int; v: 0 < 'm; z: 'C['m -@ 1]
 >- 'C['m] } ) -->
   sequent ['ext] { <H>; n: int; <J['n]> >- 'C['n] } =
      ind{'n; m, z. 'down['n; 'm; it; 'z]; 'base['n]; m, z. 'up['n; 'm; it; 'z]}

doc <:doc< 
   @begin[doc]
   @modsubsection {Induction and recursion}
   Reduction of the induction combinator @tt{ind} has three cases.
   If the argument $x$ is $0$, the combinator reduces to the @i{base}
   case; if it is positive, it reduces to the @i{up} case; and
   if it is negative, it reduces to the @i{down} case.
   The first argument in the @i{up} and @i{down} cases represents
   the induction value, and the second argument represents the
   ``next'' computational step.
   @end[doc]
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
   unfold_ind_number thenC addrC [2;0] reduce_lt thenC addrC [2] reduceTopC
 thenC addrC [0] reduce_eq_int thenC reduceTopC

(*
 * @begin[doc]
 * @modsubsection{Combinator equality}
 *
 * Two @tt{ind} term compute values of type $T$ if each of the three
 * cases (zero, positive, and negative) produces values of type $T$.
 * @end[doc]
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
prim indEquality {| intro []; eqcd |} lambda{z. 'T['z]} :
   sequent [squash] { <H> >- 'x1 = 'x2 in int } -->
   sequent [squash] { <H>; x: int; w: 'x < 0; y: 'T['x +@ 1] >- 'down1['x; 'y] =
 'down2['x; 'y] in 'T['x] } -->
   sequent [squash] { <H> >- 'base1 = 'base2 in 'T[0] } -->
   sequent [squash] { <H>; x: int; w: 0 < 'x; y: 'T['x -@ 1] >- 'up1['x; 'y] =
 'up2['x; 'y] in 'T['x] } -->
   sequent ['ext] { <H> >- ind{'x1; i1, j1. 'down1['i1; 'j1]; 'base1; k1, l1.
 'up1['k1; 'l1]}
                   = ind{'x2; i2, j2. 'down2['i2; 'j2]; 'base2; k2, l2.
 'up2['k2; 'l2]}
                   in 'T['x1] } =
  it

doc <:doc< 
   @begin[doc]
   @modsubsection{Addition properties}
  
   @tt{add} is commutative and associative.
  
   @end[doc]
>>
prim add_Commut :
   [wf] sequent [squash] { <H> >- 'a in int } -->
   [wf] sequent [squash] { <H> >- 'b in int } -->
   sequent ['ext] { <H> >- ('a +@ 'b) ~ ('b +@ 'a) } = it

interactive_rw add_Commut_rw :
   ( 'a in int ) -->
   ( 'b in int ) -->
   ('a +@ 'b) <--> ('b +@ 'a)

let add_CommutC = add_Commut_rw

interactive lt_add_lt :
   [main] sequent [squash] { <H> >- 'a < 'b} -->
   [main] sequent [squash] { <H> >- 'c < 'd} -->
   [wf] sequent [squash] { <H> >- 'a in int } -->
   [wf] sequent [squash] { <H> >- 'b in int } -->
   [wf] sequent [squash] { <H> >- 'c in int } -->
   [wf] sequent [squash] { <H> >- 'd in int } -->
   sequent ['ext] { <H> >- ('a +@ 'c) < ('b +@ 'd) }

let lt_add_ltT = lt_add_lt

prim add_Assoc :
   [wf] sequent [squash] { <H> >- 'a in int } -->
   [wf] sequent [squash] { <H> >- 'b in int } -->
   [wf] sequent [squash] { <H> >- 'c in int } -->
   sequent ['ext] { <H> >- ('a +@ ('b +@ 'c)) ~ (('a +@ 'b) +@ 'c) } = it

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
   @begin[doc]
  
   0 is neutral element for @tt{add} in @tt{int}
  
   @end[doc]
>>
prim add_Id :
   [wf] sequent [squash] { <H> >- 'a in int } -->
   sequent ['ext] { <H> >- ('a +@ 0) ~ 'a } = it

interactive_rw add_Id_rw {| reduce |} :
   ( 'a in int ) -->
   ('a +@ 0) <--> 'a

let add_IdC = add_Id_rw

interactive_rw add_Id2_rw {| reduce |} :
   ( 'a in int ) -->
   (0 +@ 'a) <--> 'a

let add_Id2C = add_Id2_rw

interactive_rw add_Id3_rw :
   ( 'a in int ) -->
   'a <--> (0 +@ 'a)

let add_Id3C = add_Id3_rw

interactive_rw add_Id4_rw :
   ( 'a in int ) -->
   'a <--> ('a +@ 0)

let add_Id4C = add_Id4_rw

doc <:doc<
   @begin[doc]

   @tt{- 'a} is a inverse element for 'a in @tt{int}

   @end[doc]
>>
prim minus_add_inverse :
   [wf] sequent [squash] { <H> >- 'a in int } -->
   sequent ['ext] { <H> >- ( 'a +@ (- 'a ) ) ~ 0 } = it

interactive_rw minus_add_inverse_rw {| reduce |} :
   ( 'a in int ) -->
   ( 'a +@ (- 'a) ) <--> 0

let minus_add_inverseC = minus_add_inverse_rw
(*
let unfold_zeroC t = foldC (mk_add_term t (mk_minus_term t)) minus_add_inverseC

interactive minus_add_inverse2 :
   [wf] sequent [squash] { <H> >- 'c in int } -->
   sequent ['ext] { <H> >- 0 ~ ('c +@ (- 'c)) }
*)
(*
interactive add_Functionality :
   [main] sequent ['ext] { <H> >- 'a ~ 'b } -->
   [wf] sequent ['ext] { <H> >- 'a in int } -->
   [wf] sequent ['ext] { <H> >- 'b in int } -->
   [wf] sequent ['ext] { <H> >- 'c in int } -->
   sequent ['ext] { <H> >- ('a +@ 'c) ~ ('b +@ 'c) }
*)
interactive add_Functionality 'c :
   [main] sequent ['ext] { <H> >- ('a +@ 'c) ~ ('b +@ 'c) } -->
   [wf] sequent ['ext] { <H> >- 'a in int } -->
   [wf] sequent ['ext] { <H> >- 'b in int } -->
   [wf] sequent ['ext] { <H> >- 'c in int } -->
   sequent ['ext] { <H> >- 'a ~ 'b }

interactive_rw add_Functionality_rw 'b 'c :
   (('a +@ 'c) ~ ('b +@ 'c)) -->
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   'a <--> 'b

let add_FunctionalityC = add_Functionality_rw

interactive minus_add_Distrib :
   [wf] sequent [squash] { <H> >- 'a in int } -->
   [wf] sequent [squash] { <H> >- 'b in int } -->
   sequent ['ext] { <H> >- (-('a +@ 'b)) ~ ((-'a) +@ (-'b)) }

interactive minus_minus_reduce :
   [wf] sequent [squash] { <H> >- 'a in int } -->
   sequent ['ext] { <H> >- (-(-'a)) ~ 'a }

interactive_rw minus_minus_reduce_rw {| reduce |} :
   ('a in int) -->
   (-(-'a)) <--> 'a

let minus_minus_reduceC = minus_minus_reduce_rw

interactive_rw minus_same_rw {| reduce |} :
   ('a in int) -->
   ('a -@ 'a) <--> 0

interactive_rw plus_minus_rw {| reduce |} :
   ('a in int) -->
   ('b in int) -->
   (('a +@ 'b) -@ 'b) <--> 'a

interactive_rw minus_plus_rw {| reduce |} :
   ('a in int) -->
   ('b in int) -->
   (('a -@ 'b) +@ 'b) <--> 'a

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
   << ('a < 'a) >>, (unfold_lt thenC (addrC [0] lt_irreflex_rw));
   <<ind{number[n:n]; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}>>, reduce_ind_numberC;
]
