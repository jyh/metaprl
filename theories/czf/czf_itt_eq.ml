(*!
 * @begin[spelling]
 * Ref Sym Trans eq dfun eqSet setSubstT
 * @end[spelling]
 *
 * @begin[doc]
 * @theory[Czf_itt_eq]
 *
 * The @tt{Czf_itt_eq} module defines @emph{extensional} equality
 * of sets.  Sets are equal if they have the same members, and in addition
 * the equality must be @emph{computable}.  The basic definition of
 * equality is given with the @tt{eq} term, which is defined
 * as follows.
 *
 * $$
 * @begin[array, l]
 * @line{@item{@eq{@collect{x_1; T_1; f_1[x_1]}; @collect{x_2; T_2; f_2[x_2]}} @equiv}}
 * @line{@item{@space @space @space
 *   @forall x_1@colon T_1. @exists x_2@colon T_2. @eq{f_{1}[x_1]; f_{2}[x_2]}}}
 * @line{@item{@space @space @space
 *   @wedge @forall x_2@colon T_2. @exists x_1@colon T_2. @eq{f_{1}[x_1]; f_{2}[x_2]}}}
 * @end[array]
 * $$
 *
 * This recursive definition requires that for each element of one set,
 * there must be an equal element in the other set.  The proof of an
 * equality is a pair of functions that, given an element of one set,
 * produce the equal element in the other set.  Note that there is
 * significant computational content in this judgment.
 *
 * The @tt{eq} judgment is a predicate in $@univ{1}$ for any two
 * sets.  The $@equal{s_1; s_2}$ judgment adds the additional requirement
 * $@isset{s_1} @wedge @isset{s_2}$ (which raises it to a predicate
 * in $@univ{2}$).
 *
 * In addition to the equality judgments, the @tt{Czf_itt_eq} module
 * also defines @emph{functionality} judgments.  The $@funset{s; f[s]}$
 * requires that the function $f$ compute equal set values for equal
 * set arguments.  The $@funprop{s; P[s]}$ requires that for any two
 * equal sets $s_1$ and $s_2$: $P[s_1] @Rightarrow P[s_2]$.  The
 * @tt{dfun_prop} term is even more stringent.  In the judgment
 * $@dfunprop{x; A; B[x]}$, the term $A$ is a type, and $B[x]$ is
 * a type for any $x @in A$.  The judgment requires that a proof
 * $B[u_2]$ be computable from @emph{any} two proofs $u_1@colon A$
 * and $u_2@colon A$ and a proof $B[u_1]$:
 *
 * $$
 * @dfunprop{x; A; B[x]} @equiv u_1@colon A @rightarrow
 *      B[u_1] @rightarrow u_2@colon A @rightarrow B[u_2].
 * $$
 *
 * The @tt{dfun_prop} term is used for functionality judgments
 * on dependent types.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey
 * @email{jyh@cs.cornell.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Czf_itt_set
(*! @docoff *)

open Itt_equal

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Sequent
open Tactic_type.Tacticals
open Var
open Mptop

open Base_auto_tactic

open Itt_equal
open Itt_rfun
open Itt_struct

open Czf_itt_set

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 * @end[doc]
 *)
declare eq{'s1; 's2}
declare equal{'s1; 's2}
declare fun_set{z. 'f['z]}
declare fun_prop{z. 'P['z]}
declare dfun_prop{u. 'A['u]; x, y. 'B['x; 'y]}
(*! @docoff *)

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let equal_term = << equal{'s1; 's2} >>
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

(*!
 * @begin[doc]
 * @rewrites
 *
 * The @tt{eq} judgment requires that the two sets
 * have the same elements.
 * @end[doc]
 *)
prim_rw unfold_eq : eq{'s1; 's2} <-->
   set_ind{'s1; T1, f1, g1.
      set_ind{'s2; T2, f2, g2.
         ((all y1 : 'T1. exst y2: 'T2. eq{.'f1 'y1; .'f2 'y2})
         & (all y2 : 'T2. exst y1: 'T1. eq{.'f1 'y1; .'f2 'y2}))}}

interactive_rw reduce_eq : eq{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} <-->
   ((all y1 : 'T1. exst y2: 'T2. eq{.'f1['y1]; .'f2['y2]})
    & (all y2 : 'T2. exst y1: 'T1. eq{.'f1['y1]; .'f2['y2]}))
(*! @docoff *)

let resource reduce +=
   << eq{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} >>, reduce_eq

(*!
 * @begin[doc]
 * The @tt{unfold_equal} term requires that, in addition, the two arguments
 * must be sets.
 * @end[doc]
 *)
prim_rw unfold_equal : equal{'s1; 's2} <-->
   ((isset{'s1} & isset{'s2}) & eq{'s1; 's2})

interactive_rw reduce_equal : equal{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} <-->
   ((isset{collect{'T1; x1. 'f1['x1]}} & isset{collect{'T2; x2. 'f2['x2]}})
   & ((all y1 : 'T1. exst y2: 'T2. eq{.'f1['y1]; .'f2['y2]})
     & (all y2 : 'T2. exst y1: 'T1. eq{.'f1['y1]; .'f2['y2]})))
(*! @docoff *)

let resource reduce +=
   << equal{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} >>, reduce_equal

(*!
 * @begin[doc]
 * The following four rewrites define the functionality judgments.
 * @end[doc]
 *)
prim_rw unfold_fun_set : fun_set{z. 'f['z]} <-->
    (all s1: set. all s2: set. (equal{'s1; 's2} => equal{'f['s1]; 'f['s2]}))

prim_rw unfold_fun_prop : fun_prop{z. 'P['z]} <-->
    (all s1: set. all s2: set. (equal{'s1; 's2} => 'P['s1] => 'P['s2]))

(*
 * This is _pointwise_ functionality.
 *)
prim_rw unfold_dfun_prop : dfun_prop{u. 'A['u]; x, y. 'B['x; 'y]} <-->
  (all s1: set. all s2: set. (equal{'s1; 's2} => (u1: 'A['s1] -> 'B['s1; 'u1] -> u2: 'A['s2] -> 'B['s2; 'u2])))
(*! @docoff *)

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

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Typehood and equality}
 * The @tt{eq} judgment is well-formed if both arguments are
 * sets.  The @emph{equality} if the @tt{eq} judgment requires
 * the set arguments to be equal (in the native @hrefterm[set] type).
 * @end[doc]
 *)
interactive eq_equality1 {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- Itt_equal!equal{univ[1:l]; eq{'s1; 's2}; eq{'s1; 's2}} }

(*
 * Membership in a universe.
 *)
interactive eq_type {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- "type"{eq{'s1; 's2}} }

(*
 * More general equality in a universe.
 *)
interactive eq_equality2 {| intro [] |} 'H :
   sequent [squash] { 'H >- Itt_equal!equal{set; 's1; 's3} } -->
   sequent [squash] { 'H >- Itt_equal!equal{set; 's2; 's4} } -->
   sequent ['ext] { 'H >- Itt_equal!equal{univ[1:l]; eq{'s1; 's2}; eq{'s3; 's4}} }

(*!
 * @begin[doc]
 * The @tt{eq} judgment also requires the arguments to be sets,
 * but in addition, and equality judgment $@equal{s_1; s_2}$ @emph{implies}
 * that both $s_1$ and $s_2$ are types.
 * @end[doc]
 *)
interactive equal_type {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- "type"{equal{'s1; 's2}} }

interactive equal_intro {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- isset{'s1} } -->
   [wf] sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- equal{'s1; 's2} }

(*
 * Equality is over sets.
 *)
interactive equal_isset_left 'H 's2 :
   sequent ['ext] { 'H >- equal{'s1; 's2} } -->
   sequent ['ext] { 'H >- isset{'s1} }

interactive equal_isset_right 'H 's1 :
   sequent ['ext] { 'H >- equal{'s1; 's2} } -->
   sequent ['ext] { 'H >- isset{'s2} }

(*!
 * @begin[doc]
 * @thysubsection{Equality is an equivalence relation}
 * The @tt{eq} judgment is reflexive, symmetric, and
 * transitive.
 * @end[doc]
 *)
interactive eq_ref {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- eq{'s1; 's1} }

(*
 * Symettry.
 *)
interactive eq_sym 'H :
   [wf] sequent [squash] {'H >- isset{'s1} } -->
   [wf] sequent [squash] {'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- eq{'s2; 's1} } -->
   sequent ['ext] { 'H >- eq{'s1; 's2} }

(*
 * Transitivity.
 *)
interactive eq_trans 'H 's2 :
   [wf] sequent [squash] {'H >- isset{'s1} } -->
   [wf] sequent [squash] {'H >- isset{'s2} } -->
   [wf] sequent [squash] {'H >- isset{'s3} } -->
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- eq{'s2; 's3} } -->
   sequent ['ext] { 'H >- eq{'s1; 's3} }

(*!
 * @begin[doc]
 * @thysubsection{Functionality}
 * The $@funset{z; f[z]}$ judgment implies that $f[z]$ is a
 * set for any set $z$.
 * @end[doc]
 *)
interactive eq_isset 'H 'J fun_set{z. 'f['z]} :
   sequent ['ext] { 'H; z: set; 'J['z] >- fun_set{z. 'f['z]} } -->
   sequent ['ext] { 'H; z: set; 'J['z] >- isset{'f['z]} }

(*! @docoff *)
let funSetT i p =
   let z, _ = Sequent.nth_hyp p i in
   let t = dest_isset (Sequent.concl p) in
   let t = mk_fun_set_term z t in
   let j, k = Sequent.hyp_indices p i in
      eq_isset j k t p

(*!
 * @begin[doc]
 * The @tt{eq} and @tt{equal} judgments are
 * @emph{functional} with respect to their set arguments.
 * @end[doc]
 *)
interactive eq_fun {| intro [] |} 'H :
   sequent ['ext] { 'H >- fun_set{z. 'f1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f2['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. eq{'f1['z]; 'f2['z]}} }

interactive equal_fun {| intro [] |} 'H :
   sequent ['ext] { 'H >- fun_set{z. 'f1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f2['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. equal{'f1['z]; 'f2['z]}} }

(*!
 * @begin[doc]
 * @thysubsection{Substitution}
 *
 * The following two rules define substitution.
 * Set $s_1$ can be replaced by set $s_2$ in a context
 * $P[s_1]$ if $s_1$ an $s_2$ are equal, and the
 * context $P[x]$ is @emph{functional} on set arguments.
 * @end[doc]
 *)
interactive eq_hyp_subst 'H 'J 's1 's2 (bind{v. 'P['v]}) 'z :
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- equal{'s1; 's2} } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x]; z: 'P['s2] >- 'C['x] } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- fun_prop{z. 'P['z]} } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- 'C['x] }

interactive eq_concl_subst 'H 's1 's2 (bind{v. 'C['v]}) 'z :
   sequent ['ext] { 'H >- equal{'s1; 's2} } -->
   sequent ['ext] { 'H >- 'C['s2] } -->
   sequent ['ext] { 'H >- fun_prop{z. 'C['z]} } -->
   sequent ['ext] { 'H >- 'C['s1] }

(*!
 * @begin[doc]
 * @thysubsection{Typehood of the functionality judgments}
 * The @tt{fun_set} judgment requires that it's argument
 * be a family of sets, and the @tt{fun_prop} judgment requires that
 * it's argument be a family of propositions.
 * @end[doc]
 *)
interactive fun_set_type {| intro [] |} 'H :
   sequent [squash] { 'H; z: set >- isset{'f['z]} } -->
   sequent ['ext] { 'H >- "type"{fun_set{z. 'f['z]}} }

interactive fun_prop_type {| intro [] |} 'H :
   sequent [squash] { 'H; z: set >- "type"{'f['z]} } -->
   sequent ['ext] { 'H >- "type"{fun_prop{z. 'f['z]}} }

(*!
 * @begin[doc]
 * The trivial cases, where the functionality argument
 * does not depend on the set argument, are functional.
 * The identity function is also functional.
 * @end[doc]
 *)
interactive fun_set {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'u} } -->
   sequent ['ext] { 'H >- fun_set{z. 'u} }

interactive fun_ref {| intro [] |} 'H :
   sequent ['ext] { 'H >- fun_set{z. 'z} }

interactive fun_prop {| intro [] |} 'H :
   sequent [squash] { 'H >- "type"{'P} } -->
   sequent ['ext] { 'H >- fun_prop{z. 'P} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*!
 * @begin[doc]
 * @thysubsection{Substitution}
 *
 * @begin[description]
 * @item{@tactic[setSubstT];
 *   The @tt{setSubstT} tactic @emph{substitutes} one set for
 *   another.  The usage is @tt{setSubstT $i$ $@eq{s_1; s_2}$}, which
 *   replaces all occurrences of the term $s_1$ with the term
 *   $s_2$ in clause $i$.}
 * @end[description]
 * @docoff
 * @end[doc]
 *)
let setConclSubstT t p =
   let s1, s2 = dest_eq t in
   let goal = Sequent.concl p in
   let z = maybe_new_vars1 p "v" in
   let bind = mk_xbind_term z (var_subst goal s1 z) in
      (eq_concl_subst (hyp_count_addr p) s1 s2 bind z
       thenLT [addHiddenLabelT "eq";
               addHiddenLabelT "main";
               addHiddenLabelT "wf"]) p

let setHypSubstT t i p =
   let s1, s2 = dest_eq t in
   let _, hyp = nth_hyp p i in
   let z = maybe_new_vars1 p "v" in
   let bind = mk_xbind_term z (var_subst hyp s1 z) in
   let j, k = hyp_indices p i in
      (eq_hyp_subst j k s1 s2 bind z
       thenLT [addHiddenLabelT "eq";
               addHiddenLabelT "main";
               addHiddenLabelT "wf"]) p

let setSubstT t i =
   if i = 0 then
      setConclSubstT t
   else
      setHypSubstT t i

(*!
 * @begin[doc]
 * @tactics
 *
 * @begin[description]
 * @item{@tactic[eqSetRefT], @tactic[eqSetSymT], @tactic[eqSetTransT];
 *    The three @tt{eqSet} tactics apply equivalence
 *    relation reasoning for the @hrefterm[eq] set judgment.}
 * @end[description]
 * @docoff
 * @end[doc]
 *)
let eqSetRefT p =
   eq_ref (hyp_count_addr p) p

let eqSetSymT p =
   eq_sym (hyp_count_addr p) p

let eqSetTransT t p =
   eq_trans (hyp_count_addr p) t p

(*
 * Apply reference by default.
 *)
let funSetRefT p =
   fun_ref (hyp_count_addr p) p

(*
 * Sethood.
 *)
let eqSetLeftT t p =
   equal_isset_left (hyp_count_addr p) t p

let eqSetRightT t p =
   equal_isset_right (hyp_count_addr p) t p

(*
 * Always reasonable to try reflexivity.
 *)
let resource auto += {
   auto_name = "eqSetRefT";
   auto_prec = trivial_prec;
   auto_tac = auto_wrap eqSetRefT
}

let resource auto += {
   auto_name = "funSetRefT";
   auto_prec = trivial_prec;
   auto_tac = auto_wrap funSetRefT
}

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
