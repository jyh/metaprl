(*!
 * @spelling{dprod fst snd productElimination weakProductElimination}
 *
 * @begin[doc]
 * @theory[Itt_dprod]
 *
 * The @emph{dependent product} $@prod{x; A; B}$ is a space of @emph{pairs},
 * where $A$ is a type, and $B[x]$ is a family of types indexed by $x @in A$.
 * The elements of the product space are the pairs $@pair{a; b}$, where $a @in A$
 * and $b @in B[a]$.
 *
 * The dependent product uses an @emph{intensional} membership equality.
 * The only elements are the @hrefterm[pair] terms, which allows a
 * strong elimination rule @hrefrule[productElimination] of the form:
 *
 * $$
 * @defrule{productElimination; i;
 *    @sequent{ext; {H; a@colon A; b@colon B[a]; J[@pair{a; b}]}; C[@pair{a; b}]};
 *    @sequent{ext; {H; x@colon @prod{y; A; B[u]}; J[x]}; C[x]}.}
 * $$
 *
 * Because of this intensional equality, the @tt{Itt_dprod} module is
 * primitive.  An alternative formulation would be to @emph{derive}
 * the product space from the very-dependent function @hrefterm[rfun]
 * (in the @hreftheory[Itt_rfun] module), the @hrefterm[union] (in the
 * @hreftheory[Itt_union] module), and the @hrefterm[unit] type (in the
 * and @hreftheory[Itt_union]) module).  The construction is as follows.
 *
 * First, the Boolean values are defined with the @tt{union} and @tt{unit}
 * types.
 *
 * $$
 * @begin[array; rcl]
 * @line{@item{@bool} @item{@equiv} @item{@unit + @unit}}
 * @line{@item{@bfalse} @item{@equiv} @item{@inl{@it}}}
 * @line{@item{@btrue} @item{@equiv} @item{@inr{@it}}}
 * @line{@item{@if{e_1; e_2; e_3}} @item{@equiv} @item{@decide{e_1; @_; e_2; @_; e_3}}}
 * @end[array]
 * $$
 *
 * Next, the dependent product space is defined as a function on
 * a Boolean domain.
 *
 * $$
 * @begin[array, rcl]
 * @line{@prod{x; A; B[x]} @equiv @rfun{f; x; @bool; @if{x; A; B[f(@bfalse)]}}}
 * @end[array]
 * $$
 *
 * The elements of this type are the functions that return the first
 * projection on the $@false$ argument, and the second projection on
 * the $@btrue$ argument.
 *
 * $$
 * @begin[array, rcl]
 * @line{@pair{a; b} @equiv @lambda{x; @if{x; a; b}}}
 * @line{@fst{p} @equiv @item{p(@false)}}
 * @line{@snd{p} @equiv @item{p(@btrue)}}
 * @end[array]
 * $$
 *
 * This encoding is satisfactory in all respects except for the
 * elimination form.  The problem is that the function space uses
 * an @emph{extensional} equality; the elements of the function
 * space $@rfun{f; x; @bool; @if{x; A; B[f(@false)]}}$ are not
 * just the terms $@lambda{x; @if{x; a; b}}$, but all equal functions.
 *
 * One alternative is to weaken the elimination form to a
 * more extensional version:
 *
 * $$
 * @defrule{weakProductElimination; p;
 *   @sequent{ext; {@ldots;
 *                    a@colon A; b@colon B[a];
 *                    w@colon @pair{a; b} = p @in @prod{x; A; B[x]}}; C[p]};
 *   @sequent{ext; {H; p@colon @prod{x; A; B[x]}; J[p]}; C[p]}.}
 * $$
 *
 * This rule @emph{can} be derived from the very-dependent function
 * encoding, but it is probably too weak to be useful.  For this reason
 * the @tt{Itt_dprod} module and the @tt{prod} type are defined
 * as primitive.
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
include Itt_void
include Itt_equal
include Itt_struct
include Itt_subtype
(*! @docoff *)

open Printf
open Mp_debug
open String_set
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
open Tactic_type.Conversionals

open Typeinf
open Base_dtactic

open Itt_equal
open Itt_subtype
open Itt_struct
open Itt_rfun

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_dprod%t"

(* debug_string DebugLoad "Loading itt_dprod..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The @tt{prod} term defines the dependent-product space,
 * and the @tt{pair} term defines the elements.
 * The @tt{spread} term is the induction combinator that
 * performs a pattern match on the argument @i{e}.  The
 * @tt{fst} and @tt{snd} terms are the normal projections
 * derived from the @tt{spread} term.
 * @end[doc]
 *)
declare prod{'A; x. 'B['x]}
declare prod{'A; 'B}
declare pair{'a; 'b}
declare spread{'e; u, v. 'b['u; 'v]}
define unfoldFst : fst{'e} <--> spread{'e; u, v. 'u}
define unfoldSnd : snd{'e} <--> spread{'e; u, v. 'v}
(*! @docoff *)

let dprod_term = << x: 'A * 'B['x] >>
let dprod_opname = opname_of_term dprod_term
let is_dprod_term = is_dep0_dep1_term dprod_opname
let dest_dprod = dest_dep0_dep1_term dprod_opname
let mk_dprod_term = mk_dep0_dep1_term dprod_opname

let prod_term = << 'A * 'B >>
let prod_opname = opname_of_term prod_term
let is_prod_term = is_dep0_dep0_term prod_opname
let dest_prod = dest_dep0_dep0_term prod_opname
let mk_prod_term = mk_dep0_dep0_term prod_opname

let pair_term = << pair{'a; 'b} >>
let pair_opname = opname_of_term pair_term
let is_pair_term = is_dep0_dep0_term pair_opname
let dest_pair = dest_dep0_dep0_term pair_opname
let mk_pair_term = mk_dep0_dep0_term pair_opname

let spread_term = << spread{'e; u, v. 'b['u; 'v]} >>
let spread_opname = opname_of_term spread_term
let is_spread_term = is_dep0_dep2_term spread_opname
let dest_spread = dest_dep0_dep2_term spread_opname
let mk_spread_term = mk_dep0_dep2_term spread_opname

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The @hrefterm[spread] term performs a pattern match
 * and substitutes the components of the pair into the
 * body term $c$.  This reduction is added to the
 * @hrefconv[reduceC] resource.
 * @end[doc]
 *)
prim_rw reduceSpread : spread{'u, 'v; a, b. 'c['a; 'b]} <--> 'c['u; 'v]

(*! @docoff *)
let resource reduce += << spread{pair{'u; 'v}; x, y. 'b['x; 'y]} >>, reduceSpread

(*!
 * @begin[doc]
 * The @hrefterm[fst] and @hrefterm[snd] terms are simplified forms
 * of @hrefterm[spread] that produce the first and second projections.
 * They also have derived reduction rules that are also added to the
 * @hrefconv[reduceC] resource.
 * @end[doc]
 *)
interactive_rw reduceFst : fst{pair{'a; 'b}} <--> 'a
interactive_rw reduceSnd : snd{pair{'a; 'b}} <--> 'b
(*! @docoff *)

let resource reduce +=
   [<< fst{pair{'u; 'v}} >>, reduceFst;
    << snd{pair{'u; 'v}} >>, reduceSnd]

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_prod
prec prec_spread

dform prod_df : parens :: "prec"[prec_prod] :: prod{'A; 'B} =
   pushm[0] slot{'A} " " times " " slot{'B} popm

dform prod_df2 :  parens :: "prec"[prec_prod] :: prod{'A; x. 'B} =
   slot{'x} `":" slot{'A} " " times " " slot{'B}

dform pair_prl_df : except_mode[src] :: pair{'a; 'b} =
   pushm[0] `"(" slot{'a}`"," slot{'b} `")" popm

dform pair_src_df : parens :: mode[src] :: pair{'a; 'b} =
   pushm[0] slot{'a}`"," slot{'b} popm

dform spread_prl_df1 : parens :: "prec"[prec_spread] :: except_mode[src] :: spread{'e; u, v. 'b} =
   szone pushm[1]
   keyword["match"] `" " slot{'e} `" " keyword["with"] hspace
      pair{'u; 'v} `" " Nuprl_font!rightarrow hspace
         slot{'b}
   popm ezone

dform fst_df1 : except_mode[src] :: fst{'e} =
   slot{'e} `".1"

dform snd_df1 : except_mode[src] :: snd{'e} =
   slot{'e} `".2"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext x:A * B
 * by productFormation A x
 * H >- A = A in Ui
 * H, x:A >- Ui ext B
 *)
prim productFormation 'H 'A 'x :
   [wf] sequent [squash] { 'H >- 'A IN univ[i:l] } -->
   [main] ('B['x] : sequent ['ext] { 'H; x: 'A >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] } =
   x:'A * 'B['x]

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Typehood and equality}
 *
 * The type equality is intensional.  A product type
 * $<< x: 'A * 'B['x] >>$ is a type if $A$ is a type, and
 * $B[x]$ is a family of types indexed by $x @in A$.
 * @end[doc]
 *)
prim productEquality {| intro_resource []; eqcd_resource |} 'H 'y :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H; y: 'A1 >- 'B1['y] = 'B2['y] in univ[i:l] } -->
   sequent ['ext] { 'H >- x1:'A1 * 'B1['x1] = x2:'A2 * 'B2['x2] in univ[i:l] } =
   it

(*
 * Typehood.
 *)
prim productType {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'A1} } -->
   [wf] sequent [squash] { 'H; x: 'A1 >- "type"{'A2['x]} } -->
   sequent ['ext] { 'H >- "type"{.y:'A1 * 'A2['y]} } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Introduction}
 *
 * The propositional interpretation of the product space
 * is the bounded existential $@exists{x; A; B[x]}$.  The
 * proposition is true if it is a type, and if there is
 * some element $a @in A$ where $B[a]$ is true.
 * @end[doc]
 *)
prim pairFormation {| intro_resource [] |} 'H 'a 'y :
   [wf] sequent [squash] { 'H >- 'a IN 'A } -->
   [main] ('b : sequent ['ext] { 'H >- 'B['a] }) -->
   [wf] sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- x:'A * 'B['x] } =
   'a, 'b

(*!
 * @begin[doc]
 * @thysubsection{Membership}
 *
 * The elements of the product space are the pairs.  For
 * the equality judgment to be valid, the $@prod{x; A; B[x]}$
 * term must be a type.  The first subgoal ensures that $A$ is
 * a type, and the second ensures that $B[a_1]$ is a type,
 * but $B[y]$ must be well-formed for @emph{any} element
 * $y @in A$, which is the purpose of the third subgoal.
 * @end[doc]
 *)
prim pairEquality {| intro_resource []; eqcd_resource |} 'H 'y :
   [wf] sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   [wf] sequent [squash] { 'H >- 'b1 = 'b2 in 'B['a1] } -->
   [wf] sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- ('a1, 'b1) = ('a2, 'b2) in x:'A * 'B['x] } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Elimination}
 *
 * The elimination rule performs a case analysis on the
 * hypothesis $x@colon @prod{x; A; B[x]}$.  The @emph{only}
 * elements are the pairs, and the rule splits the hypothesis
 * into its parts.  The proof extract term is the @hrefterm[spread]
 * induction combinator.
 * @end[doc]
 *)
prim productElimination {| elim_resource [ThinOption thinT] |} 'H 'J 'z 'u 'v :
   [wf] ('t['u; 'v] : sequent ['ext] { 'H; z: x:'A * 'B['x]; u: 'A; v: 'B['u]; 'J['u, 'v] >- 'T['u, 'v] }) -->
   sequent ['ext] { 'H; z: x:'A * 'B['x]; 'J['z] >- 'T['z] } =
   spread{'z; u, v. 't['u; 'v]}

(*!
 * @docoff
 * The equality reasoning requires type inference.
 *)
let d_spread_equalT tac p =
   let rt, spread, _ = dest_equal (Sequent.concl p) in
   let u, v, a = maybe_new_vars3 p "u" "v" "a" in
   let type_type = mk_xbind_term v rt in
   let _, _, pair, _ = dest_spread spread in
   let type_type, pair_type =
      try
         match get_with_args p with
            type_type :: pair_type :: _ ->
               type_type, pair_type
          | [pair_type] ->
               type_type, pair_type
          | [] ->
               raise (RefineError ("d_spread_equalT", StringError "terms are required"))
      with
         RefineError _ ->
            type_type, infer_type p pair
   in
      tac (Sequent.hyp_count_addr p) type_type pair_type u v a p

(*!
 * @begin[doc]
 * @thysubsection{Combinator equality}
 *
 * The @hrefterm[spread] combinator is well-formed if all
 * its parts are well-formed.
 * @end[doc]
 *)
prim spreadEquality {| eqcd_resource |} 'H bind{z. 'T['z]} (w:'A * 'B['w]) 'u 'v 'a :
   [wf] sequent [squash] { 'H >- 'e1 = 'e2 in w:'A * 'B['w] } -->
   [wf] sequent [squash] { 'H; u: 'A; v: 'B['u]; a: 'e1 = ('u, 'v) in w:'A * 'B['w] >-
             'b1['u; 'v] = 'b2['u; 'v] in 'T['u, 'v] } -->
   sequent ['ext] { 'H >- spread{'e1; u1, v1. 'b1['u1; 'v1]} = spread{'e2; u2, v2. 'b2['u2; 'v2]} in 'T['e1] } =
   it

(*! @docoff *)
let spread_equal_term = << spread{'e1; u1, v1. 'b1['u1; 'v1]} = spread{'e2; u2, v2. 'b2['u2; 'v2]} in 'T >>

let resource intro += (spread_equal_term, d_spread_equalT spreadEquality)

(*!
 * @begin[doc]
 * @thysubsection{Subtyping}
 *
 * The subtype judgment is @emph{covariant} in the
 * first type $A$, and pointwise-covariant in the second
 * type $B[a]$ for each $a @in A$.
 * @end[doc]
 *)
prim productSubtype {| intro_resource [] |} 'H 'a :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H; a: 'A1 >- subtype{'B1['a]; 'B2['a]} } -->
   sequent ['ext] { 'H >- subtype{ (a1:'A1 * 'B1['a1]); (a2:'A2 * 'B2['a2]) } } =
   it
(*! @docoff *)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (dprod_term, infer_univ_dep0_dep1 dest_dprod)

(*
 * Type of pair.
 *)
let inf_pair inf consts decls eqs opt_eqs defs t =
   let a, b = dest_pair t in
   let eqs', opt_eqs', defs', a' = inf consts decls eqs opt_eqs defs a in
   let eqs'', opt_eqs'', defs'', b' = inf consts decls eqs' opt_eqs' defs' b in
      eqs'', opt_eqs'', defs'', mk_prod_term a' b'

let resource typeinf += (pair_term, inf_pair)

(*
 * Type of spread.
 *)
let inf_spread inf consts decls eqs opt_eqs defs t =
   let u, v, a, b = dest_spread t in
   let eqs', opt_eqs', defs', a' = inf consts decls eqs opt_eqs defs a in
   let eqs'', opt_eqs'', _, a'' =
      Typeinf.typeinf_final consts eqs' opt_eqs' defs' a' in
   let consts = StringSet.add u (StringSet.add v consts) in
   if is_dprod_term a'' then
      let x, l, r = dest_dprod a' in
         inf consts ((v,subst1 r x (mk_var_term u))::(u,l)::decls) eqs'' opt_eqs'' defs' b
   else
      let av = Typeinf.vnewname consts defs' "A" in
      let bv = Typeinf.vnewname consts defs' "B" in
      let at = mk_var_term av in
      let bt = mk_var_term bv in
         inf consts ((v,bt)::(u,at)::decls)
             (eqnlist_append_eqn eqs' a' (mk_prod_term at bt)) opt_eqs''
             ((av,<<top>>)::(bv,<<top>>)::defs') b

let resource typeinf += (spread_term, inf_spread)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two function types.
 *)
let dprod_subtypeT p =
   let a = get_opt_var_arg "x" p in
      (productSubtype (Sequent.hyp_count_addr p) a
       thenT addHiddenLabelT "subtype") p

let resource sub +=
   (DSubtype ([<< a1:'A1 * 'B1['a1] >>, << a2:'A2 * 'B2['a2] >>;
               << 'A1 >>, << 'A2 >>;
               << 'B1['a1] >>, << 'B2['a1] >>],
              dprod_subtypeT))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
