doc <:doc<
   @module[Czf_itt_eq]

   The @tt[Czf_itt_eq] module defines @emph{extensional} equality
   of sets.  Sets are equal if they have the same members, and in addition
   the equality must be @emph{computable}.  The basic definition of
   equality is given with the @tt{eq} term, which is defined
   as follows.

   $$
   @begin[array, l]
   @line{@item{@eq{@collect{x_1; T_1; f_1[x_1]}; @collect{x_2; T_2; f_2[x_2]}} @equiv}}
   @line{@item{@space @space @space
     @forall x_1@colon T_1. @exists x_2@colon T_2. @eq{f_{1}[x_1]; f_{2}[x_2]}}}
   @line{@item{@space @space @space
     @wedge @forall x_2@colon T_2. @exists x_1@colon T_2. @eq{f_{1}[x_1]; f_{2}[x_2]}}}
   @end[array]
   $$

   This recursive definition requires that for each element of one set,
   there must be an equal element in the other set.  The proof of an
   equality is a pair of functions that, given an element of one set,
   produce the equal element in the other set.  Note that there is
   significant computational content in this judgment.

   The @tt{eq} judgment is a predicate in $@univ{1}$ for any two
   sets.  The $@equal{s_1; s_2}$ judgment adds the additional requirement
   $@isset{s_1} @wedge @isset{s_2}$ (which raises it to a predicate
   in $@univ{2}$).

   In addition to the equality judgments, the @tt{Czf_itt_eq} module
   also defines @emph{functionality} judgments.  The $@funset{s; f[s]}$
   requires that the function $f$ compute equal set values for equal
   set arguments.  The $@funprop{s; P[s]}$ requires that for any two
   equal sets $s_1$ and $s_2$: $P[s_1] @Rightarrow P[s_2]$.  The
   @tt{dfun_prop} term is even more stringent.  In the judgment
   $@dfunprop{x; A; B[x]}$, the term $A$ is a type, and $B[x]$ is
   a type for any $x @in A$.  The judgment requires that a proof
   $B[u_2]$ be computable from @emph{any} two proofs $u_1@colon A$
   and $u_2@colon A$ and a proof $B[u_1]$:

   $$
   @dfunprop{x; A; B[x]} @equiv u_1@colon A @rightarrow
        B[u_1] @rightarrow u_2@colon A @rightarrow B[u_2].
   $$

   The @tt{dfun_prop} term is used for functionality judgments
   on dependent types.

   @docoff
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

   Author: Jason Hickey
   @email{jyh@cs.cornell.edu}
   @end[license]
>>

doc <:doc< @parents >>
extends Czf_itt_set
doc docoff

open Itt_equal

open Basic_tactics

open Itt_equal
open Itt_rfun

open Czf_itt_set

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc terms
declare eq{'s1; 's2}
declare equal{'s1; 's2}
declare fun_set{z. 'f['z]}
declare fun_prop{z. 'P['z]}
declare dfun_prop{u. 'A['u]; x, y. 'B['x; 'y]}
doc docoff

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let equal_term = << 's1 = 's2 >>
let equal_opname = opname_of_term equal_term
let is_eq_term = is_dep0_dep0_term equal_opname
let dest_eq = dest_dep0_dep0_term equal_opname
let mk_eq_term = mk_dep0_dep0_term equal_opname

let fun_set_term = << fun_set{z. 's['z]} >>
let fun_set_opname = opname_of_term fun_set_term
let is_fun_set_term = is_dep1_term fun_set_opname
let dest_fun_set = dest_dep1_term fun_set_opname
let mk_fun_set_term = mk_dep1_term fun_set_opname

let fun_prop_term = << fun_prop{z. 's['z]} >>
let fun_prop_opname = opname_of_term fun_prop_term
let is_fun_prop_term = is_dep1_term fun_prop_opname
let dest_fun_prop = dest_dep1_term fun_prop_opname
let mk_fun_prop_term = mk_dep1_term fun_prop_opname

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @rewrites

   The @tt{eq} judgment requires that the two sets
   have the same elements.
>>
prim_rw unfold_eq : eq{'s1; 's2} <-->
   set_ind{'s1; T1, f1, g1.
      set_ind{'s2; T2, f2, g2.
         ((all y1 : 'T1. exst y2: 'T2. eq{.'f1 'y1; .'f2 'y2})
         & (all y2 : 'T2. exst y1: 'T1. eq{.'f1 'y1; .'f2 'y2}))}}

interactive_rw reduce_eq {| reduce |} : eq{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} <-->
   ((all y1 : 'T1. exst y2: 'T2. eq{.'f1['y1]; .'f2['y2]})
    & (all y2 : 'T2. exst y1: 'T1. eq{.'f1['y1]; .'f2['y2]}))

doc <:doc<
   The @tt{unfold_equal} term requires that, in addition, the two arguments
   must be sets.
>>
prim_rw unfold_equal : ('s1='s2) <-->
   ((isset{'s1} & isset{'s2}) & eq{'s1; 's2})

interactive_rw reduce_equal {| reduce |} : (collect{'T1; x1. 'f1['x1]} = collect{'T2; x2. 'f2['x2]}) <-->
   ((isset{collect{'T1; x1. 'f1['x1]}} & isset{collect{'T2; x2. 'f2['x2]}})
   & ((all y1 : 'T1. exst y2: 'T2. eq{.'f1['y1]; .'f2['y2]})
     & (all y2 : 'T2. exst y1: 'T1. eq{.'f1['y1]; .'f2['y2]})))

doc <:doc<
   The following four rewrites define the functionality judgments.
>>
prim_rw unfold_fun_set : fun_set{z. 'f['z]} <-->
    (all s1: set. all s2: set. ('s1 = 's2 => 'f['s1] = 'f['s2]))

prim_rw unfold_fun_prop : fun_prop{z. 'P['z]} <-->
    (all s1: set. all s2: set. ('s1 = 's2 => 'P['s1] => 'P['s2]))

(*
 * This is _pointwise_ functionality.
 *)
prim_rw unfold_dfun_prop : dfun_prop{u. 'A['u]; x, y. 'B['x; 'y]} <-->
  (all s1: set. all s2: set. ('s1 = 's2 => (u1: 'A['s1] -> 'B['s1; 'u1] -> u2: 'A['s2] -> 'B['s2; 'u2])))
doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform equal_df : except_mode[src] :: parens :: "prec"[prec_equal] :: equal{'s1; 's2} =
   slot{'s1} `" =' " slot{'s2}

dform eq_df : except_mode[src] :: eq{'s1; 's2} =
   `"eq(" slot {'s1} `"; " slot{'s2} `")"

dform fun_set_df : except_mode[src] :: parens :: "prec"[prec_apply] :: fun_set{x. 'P} =
   Nuprl_font!forall slot{'x} `"." slot{'P} `" fun_set"

dform fun_set_df : except_mode[src] :: parens :: "prec"[prec_apply] :: fun_prop{x. 'P} =
   Nuprl_font!forall slot{'x} `"." slot{'P} `" fun_prop"

dform dfun_prop_df : except_mode[src] :: parens :: "prec"[prec_apply] :: dfun_prop{u. 'A; x, y. 'P} =
   szone pushm[0]
   Nuprl_font!forall slot{'u} `":" slot{'A} `"." hspace slot{'x} `"," slot{'y} `"." slot{'P} `" fun_prop"
   popm ezone

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Typehood and equality}
   The @tt{eq} judgment is well-formed if both arguments are
   sets.  The @emph{equality} if the @tt{eq} judgment requires
   the set arguments to be equal (in the native @hrefterm[set] type).
>>
interactive eq_equality1 {| intro [] |} :
   sequent { <H> >- isset{'s1} } -->
   sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- eq{'s1; 's2} =  eq{'s1; 's2} in univ[1:l] }

(*
 * Membership in a universe.
 *)
interactive eq_type {| intro [] |} :
   sequent { <H> >- isset{'s1} } -->
   sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- "type"{eq{'s1; 's2}} }

(*
 * More general equality in a universe.
 *)
interactive eq_equality2 {| intro [] |} :
   sequent { <H> >- 's1 = 's3 in set } -->
   sequent { <H> >- 's2 = 's4 in set } -->
   sequent { <H> >-  eq{'s1; 's2}=  eq{'s3; 's4} in univ[1:l]  }

doc <:doc<
   The @tt{eq} judgment also requires the arguments to be sets,
   but in addition, and equality judgment $@equal{s_1; s_2}$ @emph{implies}
   that both $s_1$ and $s_2$ are types.
>>
interactive equal_type {| intro [] |} :
   sequent { <H> >- isset{'s1} } -->
   sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- "type"{.'s1='s2} }

interactive equal_intro {| intro [] |} :
   [wf] sequent { <H> >- isset{'s1} } -->
   [wf] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- eq{'s1; 's2} } -->
   sequent { <H> >- 's1 = 's2 }

(*
 * Equality is over sets.
 *)
interactive equal_isset_left 's2 :
   sequent { <H> >- equal{'s1; 's2} } -->
   sequent { <H> >- isset{'s1} }

interactive equal_isset_right 's1 :
   sequent { <H> >- equal{'s1; 's2} } -->
   sequent { <H> >- isset{'s2} }

doc <:doc<
   @modsubsection{Equality is an equivalence relation}
   The @tt{eq} judgment is reflexive, symmetric, and
   transitive.
>>
interactive eq_ref {| intro [] |} :
   sequent { <H> >- isset{'s1} } -->
   sequent { <H> >- eq{'s1; 's1} }

(*
 * Symettry.
 *)
interactive eq_sym :
   [wf] sequent { <H> >- isset{'s1} } -->
   [wf] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- eq{'s2; 's1} } -->
   sequent { <H> >- eq{'s1; 's2} }

(*
 * Transitivity.
 *)
interactive eq_trans 's2 :
   [wf] sequent { <H> >- isset{'s1} } -->
   [wf] sequent { <H> >- isset{'s2} } -->
   [wf] sequent { <H> >- isset{'s3} } -->
   sequent { <H> >- eq{'s1; 's2} } -->
   sequent { <H> >- eq{'s2; 's3} } -->
   sequent { <H> >- eq{'s1; 's3} }

doc <:doc<
   @modsubsection{Functionality}
   The $@funset{z; f[z]}$ judgment implies that $f[z]$ is a
   set for any set $z$.
>>
interactive eq_isset 'H fun_set{z. 'f['z]} :
   sequent { <H>; z: set; <J['z]> >- fun_set{z. 'f['z]} } -->
   sequent { <H>; z: set; <J['z]> >- isset{'f['z]} }

doc docoff
let funSetT = argfunT (fun i p ->
   let z = Sequent.nth_binding p i in
   let t = dest_isset (Sequent.concl p) in
   let t = mk_fun_set_term z t in
      eq_isset (Sequent.get_pos_hyp_num p i) t)

doc <:doc<
   The @tt{eq} and @tt{equal} judgments are
   @emph{functional} with respect to their set arguments.
>>
interactive eq_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 'f1['z]} } -->
   sequent { <H> >- fun_set{z. 'f2['z]} } -->
   sequent { <H> >- fun_prop{z. eq{'f1['z]; 'f2['z]}} }

interactive equal_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 'f1['z]} } -->
   sequent { <H> >- fun_set{z. 'f2['z]} } -->
   sequent { <H> >- fun_prop{z. 'f1['z] = 'f2['z]} }

doc <:doc<
   @modsubsection{Substitution}

   The following two rules define substitution.
   Set $s_1$ can be replaced by set $s_2$ in a context
   $P[s_1]$ if $s_1$ an $s_2$ are equal, and the
   context $P[x]$ is @emph{functional} on set arguments.
>>
interactive eq_hyp_subst 'H 's1 's2 (bind{v. 'P['v]}) :
   sequent { <H>; x: 'P['s1]; <J['x]> >- equal{'s1; 's2} } -->
   sequent { <H>; x: 'P['s1]; <J['x]>; z: 'P['s2] >- 'C['x] } -->
   sequent { <H>; x: 'P['s1]; <J['x]> >- fun_prop{z. 'P['z]} } -->
   sequent { <H>; x: 'P['s1]; <J['x]> >- 'C['x] }

interactive eq_concl_subst 's1 's2 (bind{v. 'C['v]}) :
   sequent { <H> >- equal{'s1; 's2} } -->
   sequent { <H> >- 'C['s2] } -->
   sequent { <H> >- fun_prop{z. 'C['z]} } -->
   sequent { <H> >- 'C['s1] }

doc <:doc<
   @modsubsection{Typehood of the functionality judgments}
   The @tt{fun_set} judgment requires that it's argument
   be a family of sets, and the @tt{fun_prop} judgment requires that
   it's argument be a family of propositions.
>>
interactive fun_set_type {| intro [] |} :
   sequent { <H>; z: set >- isset{'f['z]} } -->
   sequent { <H> >- "type"{fun_set{z. 'f['z]}} }

interactive fun_prop_type {| intro [] |} :
   sequent { <H>; z: set >- "type"{'f['z]} } -->
   sequent { <H> >- "type"{fun_prop{z. 'f['z]}} }

doc <:doc<
   The trivial cases, where the functionality argument
   does not depend on the set argument, are functional.
   The identity function is also functional.
>>
interactive fun_set {| intro [] |} :
   sequent { <H> >- isset{'u} } -->
   sequent { <H> >- fun_set{z. 'u} }

interactive fun_ref {| intro [] |} :
   sequent { <H> >- fun_set{z. 'z} }

interactive fun_prop {| intro [] |} :
   sequent { <H> >- "type"{'P} } -->
   sequent { <H> >- fun_prop{z. 'P} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

doc <:doc<
   @modsubsection{Substitution}

   @begin[description]
   @item{@tactic[setSubstT];
     The @tt{setSubstT} tactic @emph{substitutes} one set for
     another.  The usage is @tt{setSubstT $i$ $@eq{s_1; s_2}$}, which
     replaces all occurrences of the term $s_1$ with the term
     $s_2$ in clause $i$.}
   @end[description]
   @docoff
>>
let setConclSubstT = argfunT (fun t p ->
   let s1, s2 = dest_eq t in
   let goal = Sequent.concl p in
   let bind = var_subst_to_bind goal s1 in
      eq_concl_subst s1 s2 bind
      thenLT [addHiddenLabelT "eq";
              addHiddenLabelT "main";
              addHiddenLabelT "wf"])

let setHypSubstT t i = funT (fun p ->
   let s1, s2 = dest_eq t in
   let hyp = nth_hyp p i in
   let bind = var_subst_to_bind hyp s1 in
      eq_hyp_subst (get_pos_hyp_num p i) s1 s2 bind
      thenLT [addHiddenLabelT "eq";
              addHiddenLabelT "main";
              addHiddenLabelT "wf"])

let setSubstT t i =
   if i = 0 then
      setConclSubstT t
   else
      setHypSubstT t i

doc <:doc<
   @tactics

   @begin[description]
   @item{@tactic[eqSetRefT], @tactic[eqSetSymT], @tactic[eqSetTransT];
      The three @tt{eqSet} tactics apply equivalence
      relation reasoning for the @hrefterm[eq] set judgment.}
   @end[description]
   @docoff
>>
let eqSetRefT = eq_ref
let eqSetSymT = eq_sym
let eqSetTransT = eq_trans

(*
 * Apply reference by default.
 *)
let funSetRefT = fun_ref

(*
 * Sethood.
 *)
let eqSetLeftT = equal_isset_left
let eqSetRightT = equal_isset_right

(*
 * Always reasonable to try reflexivity.
 *)
let resource auto += [{
   auto_name = "eqSetRefT";
   auto_prec = trivial_prec;
   auto_tac = eqSetRefT;
   auto_type = AutoNormal;
}; {
   auto_name = "funSetRefT";
   auto_prec = trivial_prec;
   auto_tac = funSetRefT;
   auto_type = AutoNormal;
}]

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
