(*!
 * @begin[spelling]
 * disect
 * @end[spelling]
 * @begin[doc]
 * @module[Itt_disect]
 *
 * The @tt{Itt_disect} module defines the @emph{dependent intersection}
 * type $@bisect{x@colon A; B[x]}$.
 * This type contains all elements $a$ from $A$ such that $a$ is also
 * in $B[a]$.
 *
 * For example if $A=@int$ and $B[x]=@set{y;@int;y>2*y}$
 * then $@bisect{x@colon A; B[x]}$ contains all integers,
 * such that $x>2*x$.
 *
 * Do not confuse dependent intersection with $@isect{x;A;B[x]}$ defined
 * in the @hrefmodule[Itt_isect] theory.
 * The latter type refers to the intersection of a family of types.
 *
 * In some sence the dependent intersection is similar to
 * the dependent product type $@prod{x;A;B[x]}$
 * (when $@isect{x;A;B[x]}$ is similar to the function space
 * $@fun{x; A; B[x]}$).
 *
 * The ordinary binary intersection can be defined just as dependent
 * intersection with a constant second argument:
 * $@bisect{A;B}=@bisect{x@colon A;B}$.
 *
 * Dependent intersection is used to represent @emph{dependent} records.
 * For example the record
 * $@record{{@tt[x]@colon A;@tt[y]@colon B[@tt[x]]}}$
 * can be defined as
 * $@bisect{x@colon @record{@tt[x]@colon A};@record{B[x.@tt[x]]}}$
 *
 * Sets also can be defined as dependent intersection
 * $@set{x;A;P[x]} = @bisect{x@colon A;squash(P[x])}$
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
 * Author: Alexei Kopylov
 * @email{kopylov@cs.cornell.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)


extends Itt_equal
extends Itt_rfun
extends Itt_set
extends Itt_isect
extends Itt_tsquash
extends Itt_subtype
extends Itt_ext_equal
(*! @docoff *)

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Var
open Tactic_type
open Tactic_type.Tacticals

open Base_auto_tactic
open Base_dtactic

open Perv
open Itt_equal
open Itt_subtype
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_disect%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The @tt{disect} term denotes the dependent intersection type.
 * @end[doc]
 *)

declare "disect"{'A; x. 'B['x]}

(*! @docoff *)

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform disect_df1 : except_mode[src] :: (disect{'A; x.'B}) =
   slot{'x} `":" slot{'A} cap slot{'B}



(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext disect x: A. B[x]
 * by dintersectionFormation x A
 * H >- A = A in Ui
 * H, x: A >- Ui ext B[x]
 *)
prim dintersectionFormation 'H 'x 'A :
   [wf] sequent [squash] { 'H >- 'A = 'A in univ[i:l] } -->
   ('B['x] : sequent ['ext] { 'H; x: 'A >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] } =
   disect{'A; x.'B['x]}

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Typehood and equality}
 *
 * The intersection $@bisect{x@colon A; B[x]}$ is well-formed if
 * $A$ is a type, and $B[x]$ is a family of types indexed by
 * $x @in A$.
 * @end[doc]
 *)

prim dintersectionEquality {| intro []; eqcd |} 'H 'y :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H; y: 'A1 >- 'B1['y] = 'B2['y] in univ[i:l] } -->
   sequent ['ext] { 'H >- disect{'A1; x1.'B1['x1]} = disect{'A2; x2.'B2['x2]} in univ[i:l] } =
   it

prim dintersectionType {| intro [] |} 'H 'y :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- "type"{.disect{'A; x. 'B['x]}} } =
   it

prim dintersectionTypeElimination {| elim [ThinOption thinT] |} 'H 'J 'a 'v:
   [wf] sequent [squash] { 'H; u:"type"{.disect{'A; x. 'B['x]}}; 'J['u]  >- 'a IN 'A } -->
   ('t['u,'v] :
   sequent ['ext] { 'H; u:"type"{.disect{'A; x. 'B['x]}}; v:"type"{'B['a]}; 'J['u] >- 'C['u] }) -->
   sequent ['ext] { 'H; u:"type"{.disect{'A; x. 'B['x]}}; 'J['u] >- 'C['u] } =
   't['u,it]

(*!
 * @begin[doc]
 * @modsubsection{Membership}
 * Two elements $t1$ and $t2$ are equal in $@bisect{x@colon A; B[x]}$ if
 * they are equal both in $A$ and in $B[t1]$.
 * That is $t @in @bisect{x@colon A; B[x]}$ if $t @in A$ and $t @in B[t]$.
 * @end[doc]
 *)


prim dintersectionMemberEquality {| intro []; eqcd |} 'H :
   [wf] sequent [squash] { 'H; x:'A >- "type"{'B['x]} } -->
   sequent [squash] { 'H >- 't1 = 't2 in 'A } -->
   sequent [squash] { 'H >- 't1 = 't2 in 'B['t1] } -->
   sequent ['ext] { 'H >- 't1 = 't2 in disect{'A; x.'B['x]} } =
   it

(*!
 * @begin[doc]
 * @modsubsection{Introduction}
 * There is no special rule for introduction.
 * The only one way to introduce dependent intersection is to present
 * its witness @emph{explicitly} and use the above rule.
 * @end[doc]
 *)

interactive dintersectionMemberFormation {| intro [] |} 'H 't:
   [wf] sequent [squash] { 'H; x:'A >- "type"{'B['x]} } -->
   sequent [squash] { 'H >- 't IN 'A } -->
   sequent [squash] { 'H >- 't IN 'B['t] } -->
   sequent ['ext] { 'H >- disect{'A; x.'B['x]} }

(*!
 * @begin[doc]
 * @modsubsection{Elimination}
 * The elimination rule for an assumption $x@colon @bisect{y@colon A;B[y]}$
 * produces two witnesses that $x @in A$ and that $x @in B[x]$
 * @end[doc]
 *)

prim disectElimination {| elim [] |} 'H 'J  bind{a,b,HACK.'T['a;'b;'HACK]}:
   [main] ('t['a; 'b] :
   sequent ['ext] { 'H; x: disect{'A; y.'B['y]}; 'J['x];  a:'A; b: 'B['a]  >- 'T['a;'b; it] }) -->
   sequent ['ext] { 'H; x: disect{'A; y.'B['y]}; 'J['x] >- 'T['x;'x; it] } =
   't['x; 'x]

(*!
 * @begin[doc]
 * As a corollary of elimination rule we have that if
 * two terms are equal in dependent the intersection, they are also
 * equal in both cases of the intersection.
 * The @tactic[disectCaseEqualityT] applies this rule
 * @end[doc]
 *)

interactive disectMemberCaseEquality1 'H (disect{'A;x.'B['x]}) :
   [wf] sequent [squash] { 'H >- 'x1 = 'x2 in disect{'A; y.'B['y]}  } -->
   sequent ['ext] { 'H >- 'x1 = 'x2 in 'A }

interactive disectMemberCaseEquality2 'H (disect{'A;x.'B['x]}) :
   [wf] sequent [squash] { 'H >- 'x1 = 'x2 in disect{'A; y.'B['y]}  } -->
   sequent ['ext] { 'H >- 'x1 = 'x2 in 'B['x1] }

let disectCaseEqualityT t p =
   let i = Sequent.hyp_count_addr p in
   let tac = disectMemberCaseEquality2 i t orelseT disectMemberCaseEquality1 i t in
      tac p

(*! @docoff *)
(* disectElimination_eq is derived from disectMemberCaseEquality1/2
   (with the help of dintersectionTypeElimination).
   Therefore we can state disectMemberCaseEquality1/2 as primitive.
   Note that in pairwise functionality we do not need dintersectionTypeElimination
   to derive disectElimination_eq.
*)

interactive disectElimination_eq {| elim [] |} 'H 'J  'u 'v bind{x,HACK.bind{a,b.'C['x;'a;'b;'HACK]}} :
   [main] sequent ['ext] { 'H; x: disect{'A; y.'B['y]}; 'J['x];
                           a: 'A; u: 'a = 'x in 'A; b: 'B['a]; v: 'b = 'x in 'B['a]  >- 'C['x;'a;'b; it] } -->
   sequent ['ext] { 'H; x: disect{'A; y.'B['y]}; 'J['x] >- 'C['x;'x;'x; it] }

let disectEliminationT n p =
   let u,v = maybe_new_vars2 p "u" "v" in
   let i, j = Sequent.hyp_indices p n in
   let x,_ = Sequent.nth_hyp p n in
   let x_var = mk_var_term x in
   let bind =  get_with_arg p in
      if is_bind2_term bind then
         let bind2 = mk_bind2_term x "HACK" bind in
            disectElimination_eq i j u v bind2 p
      else
         raise (RefineError
           ("disectElimination", StringTermError ("required the bind term:",<<bind{a,b.'C['a;'b]}>>)))

let disectEliminationT n p =
   let n = if n<0 then (Sequent.hyp_count p) + n + 1 else n in
      (disectEliminationT n thenT thinIfThinningT [-3;-1;n]) p

let resource elim += (<<disect{'A; x.'B['x]}>>,disectEliminationT)

(*!
 * @begin[doc]
 *
 * The elimination rule has also two simpler forms.
 * The first produces a witness $a$ for $A$, and the second produces two witness $a$ for $A$
 * and $b$ for $B[a]$.
 * @end[doc]
 *)


interactive disectEliminationLeft (*{| elim [SelectOption 1] |}*) 'H 'J 'a 'u 'b 'v:
   sequent ['ext] { 'H; x: disect{'A; y.'B['y]}; 'J['x];
                    a: 'A; u: 'a = 'x in 'A;  b: 'B['a]; v: 'b = 'x in 'B['a] >- 'C['a] } -->
   sequent ['ext] { 'H; x: disect{'A; y.'B['y]}; 'J['x] >- 'C['x] }

interactive disectEliminationRight (*{| elim [SelectOption 2] |}*) 'H 'J 'a 'u 'b 'v :
   sequent ['ext] { 'H; x: disect{'A; y.'B['y]}; 'J['x];
                    a: 'A; u: 'a = 'x in 'A;  b: 'B['a]; v: 'b = 'x in 'B['a] >- 'C['b] } -->
   sequent ['ext] { 'H; x: disect{'A; y.'B['y]}; 'J['x] >- 'C['x] }

let disectEliminationT n p =
   let n = if n<0 then (Sequent.hyp_count p) + n + 1 else n in
   try
      let sel = get_sel_arg p in
      let a,u,b,v = maybe_new_vars4 p "a" "u" "b" "v" in
      let i, j = Sequent.hyp_indices p n in
         if sel = 1 then (disectEliminationLeft i j a u b v thenT thinIfThinningT [-3;-1;n]) p else
         if sel = 2 then (disectEliminationRight i j a u b v thenT thinIfThinningT [-3;-1;n]) p else
            raise (RefineError ("disectElimination", StringError ("select option is out of range ([1,2])")))
   with RefineError ("get_attribute",_) ->
      try disectEliminationT n p
      with RefineError ("get_attribute",_) ->
         raise (RefineError
            ("disectElimination", StringTermError ("need a select option or a bind term:",<<bind{a,b.'C['a;'b]}>>)))

let resource elim += (<<disect{'A; x.'B['x]}>>,disectEliminationT)


(*!
 * @begin[doc]
 * @modsubsection{Subtyping}
 *
 * The dependent intersection $@bisect{x@colon A; B[x]}$ is covariant
 * in both $A$ and $B[x]$.
 * @end[doc]
 *)

prim dintersectionSubtype  'H 'a :
   [subtype] sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   [subtype] sequent [squash] { 'H; a: 'A1 >- subtype{'B1['a]; 'B2['a]} } -->
   sequent ['ext] { 'H >- subtype{ disect{'A1; a1.'B1['a1]}; disect{'A2; a2.'B2['a2]} } } =
   it

(************************************************************************
 * INTERACTIVE RULES                                                    *
 ************************************************************************)

interactive dinter_associativity 'H :
   [wf] sequent[squash] { 'H >- "type"{'A}} -->
   [wf] sequent[squash] { 'H; a:'A >- "type"{'B['a]}} -->
   [wf] sequent[squash] { 'H; a:'A; b:'B['a] >- "type"{'C['a;'b]}} -->
   sequent ['ext] { 'H >- ext_equal{
                       disect{'A;a.disect{'B['a];b.'C['a;'b]}};
                       disect{disect{'A;a.'B['a]};ab.'C['ab;'ab]}
                  }}



(*!
 * @begin[doc]
 * @modsubsection{Set type as dependent intersection}
 *
 * As an example of using dependent intersection we show that
 * sets (@hrefmodule[Itt_set]) are extensionally equal to dependent intersections.
 *
 * First let us define $[A]$ as $@set{x;Top;A}$.
 * @end[doc]
 *)


(*!
 * @begin[doc]
 * Now we can prove that
 * $@set{x;A;P[x]} = @bisect{x@colon A;[P[x]]}$
 * @end[doc]
 *)

interactive set_is_disect {| intro [] |} 'H :
   [wf] sequent[squash] { 'H >- "type"{'A}} -->
   [wf] sequent[squash] { 'H; x:'A >- "type"{'P['x]}} -->
   sequent ['ext] { 'H >- ext_equal{ {x: 'A | 'P['x]}; disect{'A;x.tsquash{'P['x]}}}}

(*! @docoff *)

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let disect_term = << disect{'A; x.'B['x]} >>
let disect_opname = opname_of_term disect_term
let is_disect_term = is_dep0_dep1_term disect_opname
let dest_disect = dest_dep0_dep1_term disect_opname
let mk_disect_term = mk_dep0_dep1_term disect_opname

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (disect_term, infer_univ_dep0_dep1 dest_disect)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two intersection types.
 *)
let disect_subtypeT p =
   let a = get_opt_var_arg "x" p in
      dintersectionSubtype (Sequent.hyp_count_addr p) a p

let resource sub +=
   (DSubtype ([<< disect{'A1; a1.'B1['a1]} >>, << disect{'A2; a2.'B2['a2]} >>;
               << 'A1 >>, << 'A2 >>;
               << 'B1['a1] >>, << 'B2['a1] >>],
              disect_subtypeT))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
