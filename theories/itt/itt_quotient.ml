(*!
 * @spelling{quot mod rem}
 *
 * @begin[doc]
 * @theory[Itt_quotient]
 *
 * The @tt{Itt_quotient} module defines the @emph{quotient}
 * type $@quot{T; x; y; E[x, y]}$, which imposes a @emph{new}
 * equality $E$ on the type $T$.  The relation $E$ must be
 * an equivalence relation on $T$; and to be well-formed the
 * new equality must be @emph{coarser} than the native
 * equality in $T$.  The elements of the quotient type are the
 * elements of $T$, but equality is determined by the relation $E$.
 *
 * One use of the quotient type is to quotient a type in a similar
 * manner as in set-theory.  For example, the following type defines
 * the integers @emph{mod} 2.
 *
 * $$@int_2 @equiv @quot{@int; i; j; i @mathrel{rem} 2 = j @mathrel{rem} 2}$$
 *
 * The even integers are equal in $@int_2$, and so are the odd integers.
 * Unlike set theory, the elements of the quotient type are not
 * equivalence classes.  They are the original elements; only the
 * equality has changed.
 *
 * Another use of the quotient is for @emph{abstraction}.  We could,
 * for example, define data type of finite sets of numbers
 * as follows:
 *
 * $$
 * @begin[array, lllll]
 * @line{@i{Set}  @equiv T               @colon @item{@univ{i}}}
 * @line{{}       @times @i{member}      @colon @item{T @rightarrow @int @rightarrow @univ{i}}}
 * @line{{}       @times @i{empty}       @colon T}
 * @line{{}       @times @i{add}         @colon @item{T @rightarrow @int @rightarrow T}}
 * @line{{}       @times @i{empty_axiom} @colon
 *          @item{@forall i@colon @int. @not{(@i{member}(@i{empty}, i))}}}
 * @line{{}       @times @i{add_axiom}  @colon
 *          @item{@forall t@colon T. @forall i, j@colon@int.
 *                   @i{member}(@i{add}(t, j), i) @Leftrightarrow}}
 * @line{{}       {}     {}             {}
 *                      @item{@i{member}(t, i) @vee i = j}}
 * @end[array]
 * $$
 *
 * The data type definition, as-is, allows the type $T$ to ``escape'' ---
 * the type $T$ is just another field in the data type.  Abstractly, we
 * are usually only concerned with the membership function --- two sets are
 * equal if they have the same elements.  If the implementation $T$ is exposed,
 * it is possible to construct functions that ``peek'' into the structure,
 * possible producing non-functional behavior (with respect to the
 * membership function).
 *
 * One way to address this problem is to use the quotient type to ``hide''
 * the implementation.  The first step is to pair the module implementation
 * with a set representative.
 *
 * $$@i{set} @equiv S@colon @i{Set} @times S.T$$
 *
 * The next step is to @emph{quotient} the construction by its membership.
 *
 * $$@i{Set}' @equiv @quot{@i{set}; S_1; S_2; @forall i@int.
 *     S_1.1.@i{member}(S_1.2, i) @Leftrightarrow S_2.1.@i{member}(S_2.2, i)}$$
 *
 * Two sets in $@i{Set}'$ are equal if-and-only-if they have the
 * same membership.  The other methods can be given wrapped definitions
 * as follows:
 *
 * $$
 * @begin[array, lcl]
 * @line{{@i{empty}'(S)}      @equiv @item{(S, S.@i{empty})}}
 * @line{{@i{member}'(S, i)}  @equiv @item{S.1.@i{member}(S.2, i)}}
 * @line{{@i{add}'(S, i)}     @equiv @item{(S.1, S.1.@i{add}(S.2, i))}}
 * @end[array]
 * $$
 *
 * The types are as follows:
 *
 * $$
 * @begin[array, lcl]
 * @line{{@i{empty}'}  @colon @item{@i{Set} @rightarrow @i{Set}'}}
 * @line{{@i{member}'} @colon @item{@i{Set}' @rightarrow @int @rightarrow @univ{i}}}
 * @line{{@i{add}'}    @colon @item{@i{Set}' @rightarrow @int @rightarrow @i{Set}'}}
 * @end[array]
 * $$
 *
 * In addition, the membership axioms @tt{empty_axiom} and @tt{add_axiom}
 * can be proved for the $@i{Set}'$ definition.
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
include Itt_equal
include Itt_set
include Itt_rfun
include Itt_struct
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

open Base_dtactic

open Itt_equal
open Itt_subtype
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_quotient%t"

(* debug_string DebugLoad "Loading itt_quotient..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The @tt{quot} type defines the quotient type $@quot{A; x; y; E[x, y]}$.
 * @end[doc]
 *)
declare "quot"{'A; x, y. 'E['x; 'y]}
(*! @docoff *)

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_quot

dform quot_df1 : except_mode[src] :: parens :: "prec"[prec_quot] :: "quot"{'A; x, y. 'E} =
   slot{'x} `", " slot{'y} `":" " " slot{'A} `" // " slot{'E}

dform quot_df2 : mode[src] :: parens :: "prec"[prec_quot] :: "quot"{'A; x, y. 'E} =
   `"quot " slot{'x} `", " slot{'y} `":" slot{'A} `" // " slot{'E}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @docoff
 * This rule is hardly likely to be used.
 *)
prim quotientFormation 'H (quot x, y: 'A // 'E['x; 'y]) 'z 'u 'v :
   [wf] sequent [squash] { 'H >- 'A = 'A in univ[i:l] } -->
   [wf] sequent [squash] { 'H; x: 'A; y: 'A >- 'E['x; 'y] = 'E['x; 'y] in univ[i:l] } -->
   [wf] sequent [squash] { 'H; x: 'A >- 'E['x; 'x] } -->
   [wf] sequent [squash] { 'H; x: 'A; y: 'A; u: 'E['x; 'y] >- 'E['y; 'x] } -->
   [wf] sequent [squash] { 'H; x: 'A; y: 'A; z: 'A; u: 'E['x; 'y]; v: 'E['y; 'z] >- 'E['x; 'z] } -->
   sequent ['ext] { 'H >- univ[i:l] } =
   quot x, y: 'A // 'E['x; 'y]

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Equality and well-formedness}
 *
 * The quotient $@quot{A; x; y; E[x, y]}$ if $A$ is a type,
 * and $E$ is an @emph{equivalence relation}:
 * @begin[itemize]
 * @item{$E$ is reflexive: $E[x, x]$}
 * @item{$E$ is symmetric: $E[x, y] @Rightarrow E[y, x]$}
 * @item{$E$ is transitive: $E[x, y] @Rightarrow E[y, z] @Rightarrow E[x, z]$}
 * @end[itemize]
 * @end[doc]
 *)
prim quotientType {| intro_resource [] |} 'H 'u 'v 'w 'x1 'x2 :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; u: 'A; v: 'A >- "type"{'E['u; 'v]} } -->
   [wf] sequent [squash] { 'H; u: 'A >- 'E['u; 'u] } -->
   [wf] sequent [squash] { 'H; u: 'A; v: 'A; x1: 'E['u; 'v] >- 'E['v; 'u] } -->
   [wf] sequent [squash] { 'H; u: 'A; v: 'A; w: 'A; x1: 'E['u; 'v]; x2: 'E['v; 'w] >- 'E['u; 'w] } -->
   sequent ['ext] { 'H >- "type"{.quot x, y: 'A // 'E['x; 'y]} } =
   it

(*!
 * @begin[doc]
 * In the @emph{weak} form, two quotient types $@quot{A_1; x; y; E_1[x, y]}$ and
 * $@quot{A_2; x; y; E_2[x, y]}$ are equal if the types $A_1$ and $A_2$ and
 * the equivalence relations $E_1$ and $E_2$ are equal.
 * @end[doc]
 *)
prim quotientWeakEquality {| intro_resource []; eqcd_resource |} 'H 'x 'y 'z 'u 'v :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H; x: 'A1; y: 'A1 >- 'E1['x; 'y] = 'E2['x; 'y] in univ[i:l] } -->
   [wf] sequent [squash] { 'H; x: 'A1 >- 'E1['x; 'x] } -->
   [wf] sequent [squash] { 'H; x: 'A1; y: 'A1; u: 'E1['x; 'y] >- 'E1['y; 'x] } -->
   [wf] sequent [squash] { 'H; x: 'A1; y: 'A1; z: 'A1; u: 'E1['x; 'y]; v: 'E1['y; 'z] >- 'E1['x; 'z] } -->
   sequent ['ext] { 'H >- quot x1, y1: 'A1 // 'E1['x1; 'y1]
                   = quot x2, y2: 'A2 // 'E2['x2; 'y2]
                   in univ[i:l]
           } =
   it

(*!
 * @begin[doc]
 * In the @emph{strong} form, two quotient types $@quot{A_1; x; y; E_1[x, y]}$ and
 * $@quot{A_2; x; y; E_2[x, y]}$ are equal if the types $A_1$ and $A_2$ are
 * equal, and their equivalence relations are @emph{extensionally} equal
 * $E_1[x, y] @Leftrightarrow E_2[x, y]$.
 * @end[doc]
 *)
prim quotientEquality {| intro_resource [SelectOption 1] |} 'H 'r 's 'v :
   [wf] sequent [squash] { 'H >- quot x1, y1: 'A1 // 'E1['x1; 'y1] = quot x1, y1: 'A1 // 'E1['x1; 'y1] in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- quot x2, y2: 'A2 // 'E2['x2; 'y2] = quot x2, y2: 'A2 // 'E2['x2; 'y2] in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H; v: 'A1 = 'A2 in univ[i:l]; r: 'A1; s: 'A1 >- 'E1['r; 's] -> 'E2['r; 's] } -->
   [wf] sequent [squash] { 'H; v: 'A1 = 'A2 in univ[i:l]; r: 'A1; s: 'A1 >- 'E2['r; 's] -> 'E1['r; 's] } -->
   sequent ['ext] { 'H >- quot x1, y1: 'A1 // 'E1['x1; 'y1] = quot x2, y2: 'A2 // 'E2['x2; 'y2] in univ[i:l] } =
   it

(*!
 * @docoff
 *)
prim quotient_memberFormation {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   [main] ('a : sequent ['ext] { 'H >- 'A }) -->
   sequent ['ext] { 'H >- quot x, y: 'A // 'E['x; 'y] } =
   'a

(*!
 * @begin[doc]
 * @thysubsection{Membership}
 *
 * In the @emph{weak} form, any two elements in $A$ are also
 * in the quotient $@quot{A; x; y; E[x, y]}$ for @emph{any}
 * equivalence relation $E$.
 * @end[doc]
 *)
prim quotient_memberWeakEquality {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   [wf] sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y] } =
   it

prim quotientMember {| intro_resource [] |}  'H :
   [wf] sequent [squash] { 'H >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   [wf] sequent [squash] { 'H >- 'l IN 'A } -->
   sequent ['ext] { 'H >- 'l IN (quot x, y: 'A // 'E['x; 'y]) } =
   it

(*!
 * @begin[doc]
 * In the @emph{strong} form, two elements $a_1$ and $a_2$ are in
 * the quotient type $@quot{A; x; y; E[x, y]}$ if they are equal
 * in $A$, and they are related with the equivalence relation $E[a_1, a_2]$.
 * @end[doc]
 *)
prim quotient_memberEquality {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   [wf] sequent [squash] { 'H >- 'a1 IN 'A } -->
   [wf] sequent [squash] { 'H >- 'a2 IN 'A } -->
   [wf] sequent [squash] { 'H >- 'E['a1; 'a2] } -->
   sequent ['ext] { 'H >- 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y] } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Elimination}
 *
 * The first two elimination forms are valid only if the goal
 * is an equality judgment.  For both cases, the judgment is true
 * if it is true for any two elements that are equal in the quotient type.
 * The difference is the ordering of the hypotheses in the subgoal.
 * @end[doc]
 *)
prim quotientElimination1 'H 'J 'v 'w 'z :
   [wf] sequent [squash] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a] >- "type"{'T['a]} } -->
   [main] sequent [squash] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a];
             v: 'A; w: 'A; z: 'E['v; 'w] >- 's['v] = 't['w] in 'T['v]
           } -->
   sequent ['ext] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a] >- 's['a] = 't['a] in 'T['a] } =
   it

prim quotientElimination2 {| elim_resource [ThinOption thinT] |} 'H 'J 'v 'w 'z :
   [wf] sequent [squash] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a] >- "type"{'T['a]} } -->
   [main] sequent [squash] { 'H; a: quot x, y: 'A // 'E['x; 'y];
             v: 'A; w: 'A; z: 'E['v; 'w]; 'J['v] >- 's['v] = 't['w] in 'T['v]
           } -->
   sequent ['ext] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a] >- 's['a] = 't['a] in 'T['a] } =
   it

(*!
 * @begin[doc]
 * An equality assumption $a_1 = a_2 @in @quot{A; x; y; E[x, y]}$ implies
 * that $E[a_1, a_2]$.
 * @end[doc]
 *)
prim quotient_equalityElimination {| elim_resource [] |} 'H 'J 'v :
   [main] ('g['v] : sequent ['ext] { 'H; x: 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y]; 'J['x]; v: squash{'E['a1; 'a2]} >- 'T['x] }) -->
   sequent ['ext] { 'H; x: 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y]; 'J['x] >- 'T['x] } =
   'g[it]

(*!
 * @begin[doc]
 * @thysubsection{Subtyping}
 *
 * The quotient $@quot{A; x; y; E[x, y]}$ is covariant in  the type $A$ and the
 * the equivalence relation $E$ (the relation must become coarser).
 * @end[doc]
 *)
prim quotientSubtype 'H 'a1 'a2 :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H; a1: 'A1; a2: 'A1 (* ; 'E1['a1; 'a2] *) >- 'E2['a1; 'a2] } -->
   sequent [squash] { 'H >- "type"{(quot x1, y1: 'A1 // 'E1['x1; 'y1])} } -->
   sequent [squash] { 'H >- "type"{(quot x2, y2: 'A2 // 'E2['x2; 'y2])} } -->
   sequent ['ext] { 'H >- subtype{ (quot x1, y1: 'A1 // 'E1['x1; 'y1]); (quot x2, y2: 'A2 // 'E2['x2; 'y2]) } } =
   it
(*! @docoff *)

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let quotient_term = << "quot"{'A; x, y. 'E['x; 'y]} >>
let quotient_opname = opname_of_term quotient_term
let is_quotient_term = is_dep0_dep2_term quotient_opname
let dest_quotient = dest_dep0_dep2_term quotient_opname
let mk_quotient_term = mk_dep0_dep2_term quotient_opname

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of quotient.
 *)
let dest_quotient_inf t =
   let x, y, a, e = dest_quotient t in
   x, a, subst1 e y (mk_var_term x)

let typeinf_resource =
   Mp_resource.improve typeinf_resource (quotient_term, infer_univ_dep0_dep1 dest_quotient_inf)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two quotient types.
 *)
let quotient_subtypeT p =
   (match Var.maybe_new_vars ["x"; "y"] (Sequent.declared_vars p) with
       [x; y] ->
          (quotientSubtype (Sequent.hyp_count_addr p) x y
           thenLT [addHiddenLabelT "subtype";
                   addHiddenLabelT "aux";
                   addHiddenLabelT "wf";
                   addHiddenLabelT "wf"])

     | _ -> failT) p

let sub_resource =
   Mp_resource.improve
   sub_resource
   (DSubtype ([<< quot x1, y1: 'A1 // 'E1['x1; 'y1] >>, << quot x2, y2: 'A2 // 'E2['x2; 'y2] >>;
               << 'A1 >>, << 'A2 >>],
              quotient_subtypeT))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
