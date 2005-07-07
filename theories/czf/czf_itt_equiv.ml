doc <:doc<
   @module[Czf_itt_equiv]

   The @tt[Czf_itt_equiv] module defines equivalence relations on sets.
   An equivalence relation is a binary relation that is reflexive,
   symmetric, and transitive.

   Two elements in a set satisfying a binary relation on the set is
   given with the @tt{equiv} term, which is defined as follows.

   $$
   @begin[array, l]
   @line{@item{@equiv{s; r; a; b} @equiv}}
   @line{@item{@space @space @space
     @isset{s} @wedge @isset{r} @wedge @isset{a} @wedge @isset{b}}}
   @line{@item{@space @space @space
     @wedge @mem{a; s} @wedge @mem{b; s}}}
   @line{@item{@space @space @space
     @wedge @mem{@pair{a; b}; r}}}
   @end[array]
   $$

   It is exclusively designed for the equivalence relation. First, the
   @tt{pair} term used in the definition is unordered, which makes sense
   since an equivalence relation is symmetric. Second, it is given as an
   assumption that $@equiv{s; r; a; a}$ is true, which corresponds to the
   reflexivity of an equivalence relation.

   The $@equiv{s; r}$ judgment decides whether $r$ is an equivalence
   relation on $s$ by judging whether all the three properties are
   satisfied.

   In addition to the equivalence judgments, the @tt{Czf_itt_equiv} module
   also defines @emph{functionality} judgments in the sense of equivalence.
   The $@equivfunset{s; r; x; f[x]}$ requires that the function $f$
   compute equivalence set values in $s$ (under equivalence relation $r$)
   for equivalence set arguments.  The $@equivfunprop{s; r; x; P[x]}$
   requires that for any two equivalence sets $s_1$ and $s_2$: $P[s_1]
   @Rightarrow P[s_2]$.


   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2002 Xin Yu, Caltech

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

   Author: Xin Yu
   @email{xiny@cs.caltech.edu}
   @end[license]
>>

doc <:doc< @parents >>
extends Czf_itt_set
extends Czf_itt_member
extends Czf_itt_pair
extends Czf_itt_set_bvd
doc docoff

open Lm_debug
open Lm_printf

open Basic_tactics

open Itt_rfun
open Czf_itt_set

let _ =
   show_loading "Loading Czf_itt_equiv%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc terms
declare equiv{'s; 'r}

doc docoff

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @rewrites

   The @tt{equiv} judgment requires that the two elements $a$
   and $b$ are both in the set $s$ and $@pair{a; b}$ is in $r$.
>>
define unfold_equiv : equiv{'s; 'r; 'a; 'b} <-->
   (((isset{'s} & isset{'r} & isset{'a} & isset{'b}) & mem{'a; 's} & mem{'b; 's}) & mem{pair{'a; 'b}; 'r})

doc <:doc<
   The following two rewrites define the functionality judgments
   in the sense of equivalence.
>>
define unfold_equiv_fun_set : equiv_fun_set{'s; 'r; z. 'f['z]} <-->
   (all a: set. all b: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b} => equiv{'s; 'r; 'f['a]; 'f['b]}))

define unfold_equiv_fun_prop : equiv_fun_prop{'s; 'r; z. 'P['z]} <-->
    (all a: set. all b: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b} => 'P['a] => 'P['b]))
doc docoff

(*define unfold_equiv_dfun_prop : equiv_dfun_prop{u. 'A['u]; x, y. 'B['x; 'y]} <-->
   (all s: set. all r: set. all a: set. all b: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b} => (u1: 'A['a] -> 'B['a; 'u1] -> u2: 'A['b] -> 'B['b; 'u2])))
*)

let fold_equiv = makeFoldC << equiv{'s; 'r; 'a; 'b} >> unfold_equiv

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let equiv_term = << equiv{'s; 'r; 'a; 'b} >>
let equiv_opname = opname_of_term equiv_term
let is_equiv_term = is_dep0_dep0_dep0_dep0_term equiv_opname
let dest_equiv = dest_dep0_dep0_dep0_dep0_term equiv_opname
let mk_equiv_term = mk_dep0_dep0_dep0_dep0_term equiv_opname

let equiv_fun_set_term = << equiv_fun_set{'s1; 'r; z. 's2['z]} >>
let equiv_fun_set_opname = opname_of_term equiv_fun_set_term
let is_equiv_fun_set_term = is_dep0_dep0_dep1_term equiv_fun_set_opname
let dest_equiv_fun_set = dest_dep0_dep0_dep1_term equiv_fun_set_opname
let mk_equiv_fun_set_term = mk_dep0_dep0_dep1_term equiv_fun_set_opname

let equiv_fun_prop_term = << equiv_fun_prop{'s1; 'r; z. 's2['z]} >>
let equiv_fun_prop_opname = opname_of_term equiv_fun_prop_term
let is_equiv_fun_prop_term = is_dep0_dep0_dep1_term equiv_fun_prop_opname
let dest_equiv_fun_prop = dest_dep0_dep0_dep1_term equiv_fun_prop_opname
let mk_equiv_fun_prop_term = mk_dep0_dep0_dep1_term equiv_fun_prop_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform equiv_df1 : parens :: except_mode[src] :: equiv{'s; 'r} =
   `"equiv(" slot{'s} `"; " slot{'r} `")"

dform equiv_df2 : parens :: except_mode[src] :: equiv{'s; 'r; 'a; 'b} =
   `"equiv(" slot{'s} `"; " slot{'r} `"; " slot{'a} `"; " slot{'b} `")"

dform equiv_fun_set_df : except_mode[src] :: parens :: "prec"[prec_apply] :: equiv_fun_set{'s; 'r; x. 'P} =
   Mpsymbols!forall slot{'x} `"." slot{'P} `" equiv_fun_set"

dform equiv_fun_prop_df : except_mode[src] :: parens :: "prec"[prec_apply] :: equiv_fun_prop{'s; 'r; z. 'P} =
   Mpsymbols!forall slot{'z} `"." slot{'P} `" equiv_fun_prop"

(*dform equiv_dfun_prop_df : except_mode[src] :: parens :: "prec"[prec_apply] :: equiv_dfun_prop{u. 'A; x, y. 'P} =
   szone pushm[0]
   Mpsymbols!forall slot{'u} `":" slot{'A} `"." hspace slot{'x} `"," slot{'y} `"." slot{'P} `" equiv_dfun_prop"
   popm ezone
*)
(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Typehood}

   Both of the @tt{equiv} judgments are well-formed if their
   arguments are sets.
>>
prim equiv_rel_type {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- isset{'r} } -->
   sequent { <H> >- "type"{equiv{'s; 'r}} } =
   it

interactive equiv_type {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- isset{'r} } -->
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- "type"{equiv{'s; 'r; 'a; 'b}} }

doc <:doc<
   @modsubsection{Definition and property}

   The binary relation @tt{equiv} is defined reflexive.
>>
prim equiv_ref_intro {| intro [] |} :
   [wf] sequent { <H> >- isset{'s} } -->
   [wf] sequent { <H> >- isset{'r} } -->
   [wf] sequent { <H> >- isset{'a} } -->
   sequent { <H> >- mem{'a; 's} } -->
   sequent { <H> >- equiv{'s; 'r; 'a; 'a} } =
   it

doc <:doc<

   An equivalence relation on a set S is a relation
   on S satisfying reflexivity, symmetry, and transitivity.
>>
(* XXX BUG: Aleksey: For now, I put "it" as an extract here, probably needs ot be fixed *)
prim equiv_rel_intro {| intro [] |} :
   [wf] sequent { <H> >- isset{'s} } -->
   [wf] sequent { <H> >- isset{'r} } -->
   ('A['a; 'x] : sequent { <H>; a: set; x: mem{'a; 's} >- equiv{'s; 'r; 'a; 'a} }) -->
   ('B['b; 'c; 'x; 'y; 'u] : sequent { <H>; b: set; c: set; x: mem{'b; 's}; y: mem{'c; 's}; u: equiv{'s; 'r; 'b; 'c} >- equiv{'s; 'r; 'c; 'b} }) -->
   ('C['d; 'e; 'f; 'x; 'y; 'z; 'u; 'v]: sequent { <H>; d: set; e: set; f: set; x: mem{'d; 's}; y: mem{'e; 's}; z: mem{'f; 's}; u: equiv{'s; 'r; 'd; 'e}; v: equiv{'s; 'r; 'e; 'f} >- equiv{'s; 'r; 'd; 'f}}) -->
   sequent { <H> >- equiv{'s; 'r} } =
   it

doc <:doc<

   The @tt{equiv} judgment is reflexive, symmetric, and transitive.
>>
(*
(*
 * Reflexity.
 *)
interactive equiv_ref :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- isset{'r} } -->
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- equiv{'s; 'r} } -->
   sequent { <H> >- mem{'a; 's} } -->
   sequent { <H> >- equiv{'s; 'r; 'a; 'a} }
*)

(*
 * Symmetry.
 *)
prim equiv_sym :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- isset{'r} } -->
(* sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
*) ('E : sequent { <H> >- equiv{'s; 'r} }) -->
   sequent { <H> >- mem{'a; 's} } -->
   sequent { <H> >- mem{'b; 's} } -->
   ('A : sequent { <H> >- equiv{'s; 'r; 'a; 'b} }) -->
   sequent { <H> >- equiv{'s; 'r; 'b; 'a} } =
   'E, 'A

(*
 * Transitivity.
 *)
prim equiv_trans 'b :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- isset{'r} } -->
(* sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
*) ('E : sequent { <H> >- equiv{'s; 'r} }) -->
   sequent { <H> >- mem{'a; 's} } -->
   sequent { <H> >- mem{'b; 's} } -->
   sequent { <H> >- mem{'c; 's} } -->
   ('A : sequent { <H> >- equiv{'s; 'r; 'a; 'b} }) -->
   ('B : sequent { <H> >- equiv{'s; 'r; 'b; 'c} }) -->
   sequent { <H> >- equiv{'s; 'r; 'a; 'c} } =
   ('E, ('A, 'B))

doc docoff
(*
 * Symmetry in another form.
 *)
prim equiv_sym1 'H :
   sequent { <H>; x: equiv{'s; 'r; 'a; 'b}; <J['x]> >- isset{'s} } -->
   sequent { <H>; x: equiv{'s; 'r; 'a; 'b}; <J['x]> >- isset{'r} } -->
(* sequent { <H>; x: equiv{'s; 'r; 'a; 'b}; <J['x]> >- isset{'a} } -->
   sequent { <H>; x: equiv{'s; 'r; 'a; 'b}; <J['x]> >- isset{'b} } -->
*) ('E['x] : sequent { <H>; x: equiv{'s; 'r; 'a; 'b}; <J['x]> >- equiv{'s; 'r} }) -->
   sequent { <H>; x: equiv{'s; 'r; 'a; 'b}; <J['x]> >- mem{'a; 's} } -->
   sequent { <H>; x: equiv{'s; 'r; 'a; 'b}; <J['x]> >- mem{'b; 's} } -->
   ('A['x; 'u] : sequent { <H>; x: equiv{'s; 'r; 'a; 'b}; <J['x]>; u: equiv{'s; 'r; 'b; 'a} >- 'C['x] }) -->
   sequent { <H>; x: equiv{'s; 'r; 'a; 'b}; <J['x]> >- 'C['x] } =
   it

doc <:doc<
   @modsubsection{Functionality}

   The $@equivfunset{s; r; z; f[z]}$ judgment implies that if $r$ is
   an equivalence relation on $s$, then for any set $z @in s$,
   $f[z]$ is a set and is also in $s$.
>>
interactive equiv_fun_isset 'H equiv_fun_set{'s; 'r; z. 'f['z]} :
   sequent { <H>; z: set; <J['z]> >- isset{'s} } -->
   sequent { <H>; z: set; <J['z]> >- isset{'r} } -->
   sequent { <H>; z: set; <J['z]> >- equiv{'s; 'r} } -->
   sequent { <H>; z: set; <J['z]> >- mem{'z; 's} } -->
   sequent { <H>; z: set; <J['z]> >- equiv_fun_set{'s; 'r; z. 'f['z]} } -->
   sequent { <H>; z: set; <J['z]> >- isset{'f['z]} }

interactive equiv_fun_mem 'H equiv_fun_set{'s; 'r; z. 'f['z]} :
   sequent { <H>; z: set; <J['z]> >- isset{'s} } -->
   sequent { <H>; z: set; <J['z]> >- isset{'r} } -->
   sequent { <H>; z: set; <J['z]> >- equiv{'s; 'r} } -->
   sequent { <H>; z: set; <J['z]> >- mem{'z; 's} } -->
   sequent { <H>; z: set; <J['z]> >- equiv_fun_set{'s; 'r; z. 'f['z]} } -->
   sequent { <H>; z: set; <J['z]> >- mem{'f['z]; 's} }

doc docoff
let equivFunSetT = argfunT (fun i p ->
   let z = Sequent.nth_binding p i in
   let t = dest_isset (Sequent.concl p) in
   let t =
      try
         let l = Sequent.get_term_list_arg p "with" in
            match l with
               [s; r] -> mk_equiv_fun_set_term s r z t
             | _ -> raise(RefineError ("equivFunSetT", StringError ("wrong number of terms")))
      with RefineError ("get_attribute",_) ->
         raise (RefineError ("equivFunSetT", StringError ("need a term list")))
   in
      equiv_fun_isset (get_pos_hyp_num p i) t)

let equivFunMemT t i = funT (fun p ->
   let z = Sequent.nth_binding p i in
   let t =
      try
         let l = Sequent.get_term_list_arg p "with" in
            match l with
               [s; r] -> mk_equiv_fun_set_term s r z t
             | _ -> raise(RefineError ("equivFunSetT", StringError ("wrong number of terms")))
      with RefineError ("get_attribute",_) ->
         raise (RefineError ("equivFunSetT", StringError ("need a term list")))
   in
      equiv_fun_mem i t)

doc <:doc<

   The two @tt{equiv} judgments are both  @emph{functional}
   with respect to their set arguments.
>>
interactive equiv_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 'f1['z]} } -->
   sequent { <H> >- fun_set{z. 'f2['z]} } -->
   sequent { <H> >- fun_set{z. 'f3['z]} } -->
   sequent { <H> >- fun_set{z. 'f4['z]} } -->
   sequent { <H> >- fun_prop{z. equiv{'f1['z]; 'f2['z]; 'f3['z]; 'f4['z]}} }

interactive equiv_rel_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 'f1['z]} } -->
   sequent { <H> >- fun_set{z. 'f2['z]} } -->
   sequent { <H> >- fun_prop{z. equiv{'f1['z]; 'f2['z]}} }

doc docoff
interactive equiv_set_fun1 {| intro [] |} :
   [wf] sequent { <H> >- isset{'a} } -->
   [wf] sequent { <H> >- isset{'b} } -->
   sequent { <H> >- fun_set{z. 'f1['z]} } -->
   sequent { <H> >- fun_set{z. 'f2['z]} } -->
   sequent { <H> >- fun_prop{z. equiv{'f1['z]; 'f2['z]; 'a; 'b}} }

interactive equiv_elem_fun1 {| intro [] |} :
   [wf] sequent { <H> >- isset{'s} } -->
   [wf] sequent { <H> >- isset{'r} } -->
   sequent { <H> >- equiv{'s; 'r} } -->
   sequent { <H> >- fun_set{z. 'f1['z]} } -->
   sequent { <H> >- fun_set{z. 'f2['z]} } -->
   sequent { <H> >- fun_prop{z. equiv{'s; 'r; 'f1['z]; 'f2['z]}} }

interactive equiv_elem_fun2 {| intro [] |} :
   [wf] sequent { <H> >- isset{'s} } -->
   [wf] sequent { <H> >- isset{'r} } -->
   [wf] sequent { <H> >- isset{'a} } -->
   sequent { <H> >- equiv{'s; 'r} } -->
   sequent { <H> >- mem{'a; 's} } -->
   sequent { <H> >- fun_set{z. 'f1['z]} } -->
   sequent { <H> >- fun_prop{z. equiv{'s; 'r; 'a; 'f1['z]}} }

interactive equiv_elem_fun3 {| intro [] |} :
   [wf] sequent { <H> >- isset{'s} } -->
   [wf] sequent { <H> >- isset{'r} } -->
   [wf] sequent { <H> >- isset{'b} } -->
   sequent { <H> >- equiv{'s; 'r} } -->
   sequent { <H> >- mem{'b; 's} } -->
   sequent { <H> >- fun_set{z. 'f1['z]} } -->
   sequent { <H> >- fun_prop{z. equiv{'s; 'r; 'f1['z]; 'b}} }

interactive equiv_elem_fun4 {| intro [] |} :
   [wf] sequent { <H> >- isset{'s} } -->
   [wf] sequent { <H> >- isset{'r} } -->
   [wf] sequent { <H> >- isset{'a} } -->
   sequent { <H> >- equiv{'s; 'r} } -->
   sequent { <H> >- mem{'a; 's} } -->
   sequent { <H> >- fun_prop{z. equiv{'s; 'r; 'a; 'z}} }

interactive equiv_elem_fun5 {| intro [] |} :
   [wf] sequent { <H> >- isset{'s} } -->
   [wf] sequent { <H> >- isset{'r} } -->
   [wf] sequent { <H> >- isset{'b} } -->
   sequent { <H> >- equiv{'s; 'r} } -->
   sequent { <H> >- mem{'b; 's} } -->
   sequent { <H> >- fun_prop{z. equiv{'s; 'r; 'z; 'b}} }

interactive equiv_elem_equiv_fun1 {| intro [] |} :
   [wf] sequent { <H> >- isset{'s} } -->
   [wf] sequent { <H> >- isset{'r} } -->
   sequent { <H> >- equiv{'s; 'r} } -->
   sequent { <H> >- equiv_fun_set{'s; 'r; z. 'f1['z]} } -->
   sequent { <H> >- equiv_fun_set{'s; 'r; z. 'f2['z]} } -->
   sequent { <H> >- equiv_fun_prop{'s; 'r; z. equiv{'s; 'r; 'f1['z]; 'f2['z]}} }

interactive equiv_elem_equiv_fun2 {| intro [] |} :
   [wf] sequent { <H> >- isset{'s} } -->
   [wf] sequent { <H> >- isset{'r} } -->
   [wf] sequent { <H> >- isset{'a} } -->
   sequent { <H> >- mem{'a; 's} } -->
   sequent { <H> >- equiv{'s; 'r} } -->
   sequent { <H> >- equiv_fun_set{'s; 'r; z. 'f1['z]} } -->
   sequent { <H> >- equiv_fun_prop{'s; 'r; z. equiv{'s; 'r; 'a; 'f1['z]}} }

interactive equiv_elem_equiv_fun3 {| intro [] |} :
   [wf] sequent { <H> >- isset{'s} } -->
   [wf] sequent { <H> >- isset{'r} } -->
   [wf] sequent { <H> >- isset{'b} } -->
   sequent { <H> >- mem{'b; 's} } -->
   sequent { <H> >- equiv{'s; 'r} } -->
   sequent { <H> >- equiv_fun_set{'s; 'r; z. 'f1['z]} } -->
   sequent { <H> >- equiv_fun_prop{'s; 'r; z. equiv{'s; 'r; 'f1['z]; 'b}} }

interactive equiv_elem_equiv_fun4 {| intro [] |} :
   [wf] sequent { <H> >- isset{'s} } -->
   [wf] sequent { <H> >- isset{'r} } -->
   [wf] sequent { <H> >- isset{'a} } -->
   sequent { <H> >- mem{'a; 's} } -->
   sequent { <H> >- equiv{'s; 'r} } -->
   sequent { <H> >- equiv_fun_prop{'s; 'r; z. equiv{'s; 'r; 'a; 'z}} }

interactive equiv_elem_equiv_fun5 {| intro [] |} :
   [wf] sequent { <H> >- isset{'s} } -->
   [wf] sequent { <H> >- isset{'r} } -->
   [wf] sequent { <H> >- isset{'b} } -->
   sequent { <H> >- mem{'b; 's} } -->
   sequent { <H> >- equiv{'s; 'r} } -->
   sequent { <H> >- equiv_fun_prop{'s; 'r; z. equiv{'s; 'r; 'z; 'b}} }

doc <:doc<
   @modsubsection{Substitution}

   The following two rules define substitution.
   Set $s_1$ can be replaced by set $s_2$ in a context
   $P[s_1]$ if $s_1$ and $s_2$ are equivalent, and the
   context $P[x]$ is @emph{functional} (in the sense of
   equivalence) on set arguments.
>>
interactive equiv_hyp_subst 'H 's 'r 's1 's2 (bind{w. 'P['w]}) :
   sequent { <H>; x: 'P['s1]; <J['x]> >- equiv{'s; 'r} } -->
   sequent { <H>; x: 'P['s1]; <J['x]> >- equiv{'s; 'r; 's1; 's2} } -->
   sequent { <H>; x: 'P['s1]; <J['x]>; z: 'P['s2] >- 'C['x] } -->
   sequent { <H>; x: 'P['s1]; <J['x]> >- equiv_fun_prop{'s; 'r; z. 'P['z]} } -->
   sequent { <H>; x: 'P['s1]; <J['x]> >- 'C['x] }

interactive equiv_concl_subst 's 'r 's1 's2 (bind{w. 'C['w]}) :
   sequent { <H> >- equiv{'s; 'r} } -->
   sequent { <H> >- equiv{'s; 'r; 's1; 's2} } -->
   sequent { <H> >- 'C['s2] } -->
   sequent { <H> >- equiv_fun_prop{'s; 'r; z. 'C['z]} } -->
   sequent { <H> >- 'C['s1] }

doc <:doc<
   @modsubsection{Typehood of the functionality judgments}

   The @tt{equiv_fun_set} judgment $@equivfunset{s; r; x; f[x]}$
   requires $s$ and $r$ be sets, $f[x]$ be a family of sets,
   and $r$ be an equivalence relation on $s$. The @tt{equiv_fun_prop}
   judgment $@equivfunprop{s; r; x; P[x]}$ requires $s$ and $r$
   be sets, $P[x]$ be a family of propositions, and $r$ be an
   equivalence relation on $s$.
>>
interactive equiv_fun_set_type {| intro [] |} :
   [wf] sequent { <H> >- isset{'s} } -->
   [wf] sequent { <H> >- isset{'r} } -->
   sequent { <H> >- equiv{'s; 'r} } -->
   sequent { <H>; z: set >- isset{'f['z]} } -->
   sequent { <H> >- "type"{equiv_fun_set{'s; 'r; z. 'f['z]}} }

interactive equiv_fun_prop_type {| intro [] |} :
   [wf] sequent { <H> >- isset{'s} } -->
   [wf] sequent { <H> >- isset{'r} } -->
   sequent { <H> >- equiv{'s; 'r} } -->
   sequent { <H>; z: set >- "type"{'f['z]} } -->
   sequent { <H> >- "type"{equiv_fun_prop{'s; 'r; z. 'f['z]}} }

doc <:doc<

   The trivial cases, where the functionality argument
   does not depend on the set argument, are functional.
   The identity function is also functional.
>>
interactive equiv_fun_set {| intro [] |} :
   [wf] sequent { <H> >- isset{'s} } -->
   [wf] sequent { <H> >- isset{'r} } -->
   sequent { <H> >- equiv{'s; 'r} } -->
   sequent { <H> >- isset{'u} } -->
   sequent { <H> >- mem{'u; 's} } -->
   sequent { <H> >- equiv_fun_set{'s; 'r; z. 'u} }

interactive equiv_fun_ref {| intro [] |} :
   [wf] sequent { <H> >- isset{'s} } -->
   [wf] sequent { <H> >- isset{'r} } -->
   sequent { <H> >- equiv{'s; 'r} } -->
   sequent { <H> >- equiv_fun_set{'s; 'r; z. 'z} }

interactive equiv_fun_prop {| intro [] |} :
   [wf] sequent { <H> >- isset{'s} } -->
   [wf] sequent { <H> >- isset{'r} } -->
   sequent { <H> >- equiv{'s; 'r} } -->
   sequent { <H> >- "type"{'P} } -->
   sequent { <H> >- equiv_fun_prop{'s; 'r; z. 'P} }

doc <:doc<
   @modsubsection{Equivalence relation and Equality}

   If $@eq{a; b}$, then $a$ is equivalent with $b$ under any equivalence
   relation. On the other hand, if $a$ and $b$ are equivalent under all
   equivalence relations, then $a$ is equal to $b$.
>>
interactive eq_equiv_elim {| elim [] |} 'H 's 'r :
   sequent { <H>; x: eq{'a; 'b}; <J['x]> >- isset{'s} } -->
   sequent { <H>; x: eq{'a; 'b}; <J['x]> >- isset{'r} } -->
   sequent { <H>; x: eq{'a; 'b}; <J['x]> >- isset{'a} } -->
   sequent { <H>; x: eq{'a; 'b}; <J['x]> >- isset{'b} } -->
   sequent { <H>; x: eq{'a; 'b}; <J['x]> >- equiv{'s; 'r} } -->
   sequent { <H>; x: eq{'a; 'b}; <J['x]> >- mem{'a; 's} } -->
   sequent { <H>; x: eq{'a; 'b}; <J['x]> >- mem{'b; 's} } -->
   sequent { <H>; x: eq{'a; 'b}; <J['x]>; y: equiv{'s; 'r; 'a; 'b} >- 'C['x] } -->
   sequent { <H>; x: eq{'a; 'b}; <J['x]> >- 'C['x] }

doc docoff
interactive equal_equiv_elim {| elim [] |} 'H 's 'r :
   sequent { <H>; x: equal{'a; 'b}; <J['x]> >- isset{'s} } -->
   sequent { <H>; x: equal{'a; 'b}; <J['x]> >- isset{'r} } -->
   sequent { <H>; x: equal{'a; 'b}; <J['x]> >- isset{'a} } -->
   sequent { <H>; x: equal{'a; 'b}; <J['x]> >- isset{'b} } -->
   sequent { <H>; x: equal{'a; 'b}; <J['x]> >- equiv{'s; 'r} } -->
   sequent { <H>; x: equal{'a; 'b}; <J['x]> >- mem{'a; 's} } -->
   sequent { <H>; x: equal{'a; 'b}; <J['x]> >- mem{'b; 's} } -->
   sequent { <H>; x: equal{'a; 'b}; <J['x]>; y: equiv{'s; 'r; 'a; 'b} >- 'C['x] } -->
   sequent { <H>; x: equal{'a; 'b}; <J['x]> >- 'C['x] }

interactive pair_eq1 {| elim [] |} 'H :
   sequent { <H>; x: eq{pair{'a; 'b}; pair{'z; 'z}}; <J['x]> >- isset{'z} } -->
   sequent { <H>; x: eq{pair{'a; 'b}; pair{'z; 'z}}; <J['x]> >- isset{'a} } -->
   sequent { <H>; x: eq{pair{'a; 'b}; pair{'z; 'z}}; <J['x]> >- isset{'b} } -->
   sequent { <H>; x: eq{pair{'a; 'b}; pair{'z; 'z}}; <J['x]>; u: eq{'a; 'b}; v: eq{'a; 'z} >- 'C['x]} -->
   sequent { <H>; x: eq{pair{'a; 'b}; pair{'z; 'z}}; <J['x]> >- 'C['x] }

(*
interactive pair_eq {| elim [] |} 'H :
   sequent { <H>; x: eq{pair{'a; 'b}; pair{'z; 'z}}; <J['x]> >- isset{'z} } -->
   sequent { <H>; x: eq{pair{'a; 'b}; pair{'z; 'z}}; <J['x]> >- isset{'a} } -->
   sequent { <H>; x: eq{pair{'a; 'b}; pair{'z; 'z}}; <J['x]> >- isset{'b} } -->
   sequent { <H>; x: eq{pair{'a; 'b}; pair{'z; 'z}}; <J['x]>; y: eq{'a; 'b} >- 'C['x]} -->
   sequent { <H>; x: eq{pair{'a; 'b}; pair{'z; 'z}}; <J['x]> >- 'C['x] }
*)
doc <:doc<
>>
interactive equiv_equal_elim {| elim [] |} 'H :
   sequent { <H>; x: (all r: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b})); <J['x]> >- isset{'s} } -->
   sequent { <H>; x: (all r: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b})); <J['x]> >- isset{'a} } -->
   sequent { <H>; x: (all r: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b})); <J['x]> >- isset{'b} } -->
   sequent { <H>; x: (all r: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b})); <J['x]> >- mem{'a; 's} } -->
   sequent { <H>; x: (all r: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b})); <J['x]> >- mem{'b; 's} } -->
   sequent { <H>; x: (all r: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b})); <J['x]>; y: equal{'a; 'b} >- 'C['x] } -->
   sequent { <H>; x: (all r: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b})); <J['x]> >- 'C['x] }

doc docoff
(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

doc <:doc<
   @modsubsection{Substitution}

   @begin[description]
   @item{@tactic[equivSubstT];
     The @tt{equivSubstT} tactic @emph{substitutes} one set for another.
     The usage is @tt{equivSubstT $@equiv{s; r; s_1; s_2}$} $i$, which
     replaces all occurrences of the term $s_1$ with the term $s_2$ in
     clause $i$.}
   @end[description]
   @docoff
>>
let equivConclSubstT = argfunT (fun t p ->
   let s, r, s1, s2 = dest_equiv t in
   let goal = Sequent.concl p in
   let bind =
      try
         let t1 = get_with_arg p in
            if is_xbind_term t1 then
               t1
            else
               raise generic_refiner_exn (* will be immedeiatelly caugh *)
      with
         RefineError _ ->
            var_subst_to_bind goal s1
   in
      equiv_concl_subst s r s1 s2 bind)

let equivHypSubstT t i = funT (fun p ->
   let s, r, s1, s2 = dest_equiv t in
   let hyp = nth_hyp p i in
   let bind =
      try
         let t1 = get_with_arg p in
            if is_xbind_term t1 then
               t1
            else
               raise generic_refiner_exn (* will be immedeiatelly caugh *)
      with
         RefineError _ ->
            var_subst_to_bind hyp s1
   in
      equiv_hyp_subst i s r s1 s2 bind)

let equivSubstT t i =
   if i = 0 then
      equivConclSubstT t
   else
      equivHypSubstT t i

doc <:doc<
   @tactics

   @begin[description]
   @item{@tactic[equivRefT], @tactic[equivSymT], @tactic[equivTransT];
      The three @tt{equiv} tactics apply equivalence
      relation reasoning for the @hrefterm[equiv] set judgment.}
   @end[description]
   @docoff
>>
let equivRefT = equiv_ref_intro
let equivSymT = equiv_sym
let equivTransT = equiv_trans
let equivSym1T = equiv_sym1

(*
 * Always reasonable to try reflexivity.
 *)
let resource auto += [{
   auto_name = "equivRefT";
   auto_prec = trivial_prec;
   auto_tac = equivRefT;
   auto_type = AutoNormal;
}]

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
