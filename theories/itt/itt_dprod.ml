doc <:doc<
   @begin[doc]
   @module[Itt_dprod]

   The @emph{dependent product} $@prod{x; A; B}$ is a space of @emph{pairs},
   where $A$ is a type, and $B[x]$ is a family of types indexed by $x @in A$.
   The elements of the product space are the pairs $@pair{a; b}$, where $a @in A$
   and $b @in B[a]$.

   The dependent product uses an @emph{intensional} membership equality.
   The only elements are the @hrefterm[pair] terms, which allows a
   strong elimination rule @hrefrule[productElimination] of the form:

   $$
   @defrule[productElimination]{i;
      <<sequent{ <H>; a: 'A; b: 'B['a]; <J[('a,'b)]> >- 'C[('a,'b)]}>>;
      <<sequent{ <H>; x: (u:'A * 'B['u]); <J['x]> >- 'C['x]}>>.}
   $$

   Because of this intensional equality, the @tt{Itt_dprod} module is
   primitive.  An alternative formulation would be to @emph{derive}
   the product space from the very-dependent function @hrefterm[rfun]
   (in the @hrefmodule[Itt_rfun] module), the @hrefterm[union] (in the
   @hrefmodule[Itt_union] module), and the @hrefterm[unit] type (in the
   and @hrefmodule[Itt_union]) module).  The construction is as follows.

   First, the Boolean values are defined with the @tt{union} and @tt{unit}
   types.

   $$
   @begin[array; rcl]
   @line{@item{@bool} @item{@equiv} @item{@unit + @unit}}
   @line{@item{@bfalse} @item{@equiv} @item{@inl{@it}}}
   @line{@item{@btrue} @item{@equiv} @item{@inr{@it}}}
   @line{@item{@if{e_1; e_2; e_3}} @item{@equiv} @item{@decide{e_1; @_; e_2; @_; e_3}}}
   @end[array]
   $$

   Next, the dependent product space is defined as a function on
   a Boolean domain.

   $$
   @begin[array, rcl]
   @line{@prod{x; A; B[x]} @equiv @rfun{f; x; @bool; @if{x; A; B[f(@bfalse)]}}}
   @end[array]
   $$

   The elements of this type are the functions that return the first
   projection on the $@false$ argument, and the second projection on
   the $@btrue$ argument.

   $$
   @begin[array, rcl]
   @line{@pair{a; b} @equiv @lambda{x; @if{x; a; b}}}
   @line{@fst{p} @equiv @item{p(@false)}}
   @line{@snd{p} @equiv @item{p(@btrue)}}
   @end[array]
   $$

   This encoding is satisfactory in all respects except for the
   elimination form.  The problem is that the function space uses
   an @emph{extensional} equality; the elements of the function
   space $@rfun{f; x; @bool; @if{x; A; B[f(@false)]}}$ are not
   just the terms $@lambda{x; @if{x; a; b}}$, but all equal functions.

   One alternative is to weaken the elimination form to a
   more extensional version:

   $$
   @defrule[weakProductElimination]{p;
     <<sequent{ math_ldots;
                      a: 'A; b: 'B['a];
                      ('a,'b) = 'p in (x:'A * 'B['x]); <J['p]> >- 'C['p]}>>;
     <<sequent{ <H>; p: (x:'A * 'B['x]); <J['p]> >- 'C['p]}>>.}
   $$

   This rule @emph{can} be derived from the very-dependent function
   encoding, but it is probably too weak to be useful.  For this reason
   the @tt{Itt_dprod} module and the @tt{prod} type are defined
   as primitive.
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

   Author: Jason Hickey
   @email{jyh@cs.cornell.edu}
   @end[license]
>>

doc <:doc< @doc{@parents} >>

extends Itt_void
extends Itt_equal
extends Itt_struct
extends Itt_subtype
doc docoff

open Lm_debug
open Lm_symbol
open Lm_printf
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Unify_mm

open Dtactic
open Top_conversionals

open Itt_equal
open Itt_subtype
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_dprod%t"

(* debug_string DebugLoad "Loading itt_dprod..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @terms

   The @tt{prod} term defines the dependent-product space,
   and the @tt{pair} term defines the elements.
   The @tt{spread} term is the induction combinator that
   performs a pattern match on the argument @i{e}.  The
   @tt{fst} and @tt{snd} terms are the normal projections
   derived from the @tt{spread} term.
   @end[doc]
>>
declare prod{'A; x. 'B['x]}
declare prod{'A; 'B}
declare pair{'a; 'b}
declare spread{'e; u, v. 'b['u; 'v]}

define iform unfold_spread3:  spread{'e; u1,u2,u3. 'b['u1; 'u2; 'u3]} <-->  spread{'e; u1,v. spread{'v; u2,u3. 'b['u1; 'u2; 'u3]}}

define unfoldFst : fst{'e} <--> spread{'e; u, v. 'u}
define unfoldSnd : snd{'e} <--> spread{'e; u, v. 'v}
doc docoff

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

doc <:doc<
   @begin[doc]
   @rewrites

   The @hrefterm[spread] term performs a pattern match
   and substitutes the components of the pair into the
   body term $c$.  This reduction is added to the
   @hrefconv[reduceC] resource.
   @end[doc]
>>
prim_rw reduceSpread {| reduce |} : spread{'u, 'v; a, b. 'c['a; 'b]} <--> 'c['u; 'v]

doc docoff

doc <:doc<
   @begin[doc]
   The @hrefterm[fst] and @hrefterm[snd] terms are simplified forms
   of @hrefterm[spread] that produce the first and second projections.
   They also have derived reduction rules that are also added to the
   @hrefconv[reduceC] resource.
   @end[doc]
>>
interactive_rw reduceFst {| reduce |} : fst{pair{'a; 'b}} <--> 'a
interactive_rw reduceSnd {| reduce |} : snd{pair{'a; 'b}} <--> 'b
doc docoff

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
   szone pushm[0]
   keyword["let"] pushm [0] hspace pair{'u; 'v} `" " keyword["="] `" " slot{'e} popm hspace
   keyword["in"] pushm[1] hspace slot{'b} popm
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
 * by productFormation A
 * H >- A = A in Ui
 * H, x:A >- Ui ext B
 *)
prim productFormation 'A :
   [wf] sequent { <H> >- 'A in univ[i:l] } -->
   [main] ('B['x] : sequent { <H>; x: 'A >- univ[i:l] }) -->
   sequent { <H> >- univ[i:l] } =
   x:'A * 'B['x]

doc <:doc<
   @begin[doc]
   @rules
   @modsubsection{Typehood and equality}

   The type equality is intensional.  A product type
   << x: 'A * 'B['x] >> is a type if $A$ is a type, and
   $B[x]$ is a family of types indexed by $x @in A$.
   @end[doc]
>>
prim productEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H>; x1: 'A1 >- 'B1['x1] = 'B2['x1] in univ[i:l] } -->
   sequent { <H> >- x1:'A1 * 'B1['x1] = x2:'A2 * 'B2['x2] in univ[i:l] } =
   it

(*
 * Typehood.
 *)
prim productType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A1} } -->
   [wf] sequent { <H>; x: 'A1 >- "type"{'A2['x]} } -->
   sequent { <H> >- "type"{x:'A1 * 'A2['x]} } =
   it

doc <:doc<
   @begin[doc]
   @modsubsection{Membership}

   The elements of the product space are the pairs.  For
   the equality judgment to be valid, the $@prod{x; A; B[x]}$
   term must be a type.  The first subgoal ensures that $A$ is
   a type, and the second ensures that $B[a_1]$ is a type,
   but $B[y]$ must be well-formed for @emph{any} element
   $y @in A$, which is the purpose of the third subgoal.
   @end[doc]
>>
prim pairEquality {| intro [] |} :
   [wf] sequent { <H> >- 'a1 = 'a2 in 'A } -->
   [wf] sequent { <H> >- 'b1 = 'b2 in 'B['a1] } -->
   [wf] sequent { <H>; x: 'A >- "type"{'B['x]} } -->
   sequent { <H> >- ('a1, 'b1) = ('a2, 'b2) in x:'A * 'B['x] } =
   it

doc <:doc<
   @begin[doc]
   @modsubsection{Introduction}

   The propositional interpretation of the product space
   is the bounded existential $@exists{x; A; B[x]}$.  The
   proposition is true if it is a type, and if there is
   some element $a @in A$ where $B[a]$ is true.
   @end[doc]
>>
interactive pairFormation {| intro [] |} 'a :
   [wf] sequent { <H> >- 'a in 'A } -->
   [main] sequent { <H> >- 'B['a] } -->
   [wf] sequent { <H>; x: 'A >- "type"{'B['x]} } -->
   sequent { <H> >- x:'A * 'B['x] }

doc <:doc<
   @begin[doc]
   @modsubsection{Elimination}

   The elimination rule performs a case analysis on the
   hypothesis $z@colon @prod{x; A; B[x]}$.  The @emph{only}
   elements are the pairs, and the rule splits the hypothesis
   into its parts.  The proof extract term is the @hrefterm[spread]
   induction combinator.
   @end[doc]
>>
prim productElimination {| elim [ThinOption thinT] |} 'H :
   ('t['z; 'x; 'y] : sequent { <H>; z: x:'A * 'B['x]; x: 'A; y: 'B['x]; <J['x, 'y]> >- 'T['x, 'y] }) -->
   sequent { <H>; z: x:'A * 'B['x]; <J['z]> >- 'T['z] } =
   spread{'z; x, y. 't['z; 'x; 'y]}

doc <:doc<
   @begin[doc]
   @modsubsection{Combinator equality}

   The @hrefterm[spread] combinator is well-formed if all
   its parts are well-formed.
   @end[doc]
>>
prim spreadEquality bind{z. 'T['z]} (w:'A * 'B['w]) :
   [wf] sequent { <H> >- 'e1 = 'e2 in w:'A * 'B['w] } -->
   [wf] sequent { <H>; u: 'A; v: 'B['u]; a: 'e1 = ('u, 'v) in w:'A * 'B['w] >-
             'b1['u; 'v] = 'b2['u; 'v] in 'T['u, 'v] } -->
   sequent { <H> >- spread{'e1; u1, v1. 'b1['u1; 'v1]} = spread{'e2; u2, v2. 'b2['u2; 'v2]} in 'T['e1] } =
   it

interactive spreadEquality_simple {| intro [intro_typeinf <<'e1>>] |} (w:'A * 'B['w]) :
   [wf] sequent { <H> >- 'e1 = 'e2 in w:'A * 'B['w] } -->
   [wf] sequent { <H>; u: 'A; v: 'B['u]; a: 'e1 = ('u, 'v) in w:'A * 'B['w] >-
             'b1['u; 'v] = 'b2['u; 'v] in 'T } -->
   sequent { <H> >- spread{'e1; u1, v1. 'b1['u1; 'v1]} = spread{'e2; u2, v2. 'b2['u2; 'v2]} in 'T }

interactive productEqElimination {| elim [] |} 'H :
   sequent { <H>; 'x1 = 'x2 in 'A; 'y1= 'y2 in 'B['x1];  <J[it]> >- 'T[it] } -->
   sequent { <H>; u: ('x1,'y1) = ('x2,'y2) in x:'A * 'B['x]; <J['u]> >- 'T['u] }

doc <:doc<
   @begin[doc]
   @modsubsection{Subtyping}

   The subtype judgment is @emph{covariant} in the
   first type $A$, and @emph{pointwise-covariant} in the second
   type $B[a]$ for each $a @in A$.
   @end[doc]
>>
interactive productSubtype {| intro [] |} :
   ["subtype"] sequent { <H> >- 'A1 subtype 'A2 } -->
   ["subtype"] sequent { <H>; a1: 'A1 >- 'B1['a1] subtype 'B2['a1] } -->
   ["subtype"] sequent { <H>; a2: 'A2 >- 'B2['a2] Type } -->
   sequent { <H> >- (a1:'A1 * 'B1['a1]) subtype (a2:'A2 * 'B2['a2]) }
doc docoff

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
   let consts = SymbolSet.add (SymbolSet.add consts u) v in
   if is_dprod_term a'' then
      let x, l, r = dest_dprod a' in
         inf consts ((v,subst1 r x (mk_var_term u))::(u,l)::decls) eqs'' opt_eqs'' defs' b
   else
      let av = Typeinf.vnewname consts defs' (Lm_symbol.add "A") in
      let bv = Typeinf.vnewname consts defs' (Lm_symbol.add "B") in
      let at = mk_var_term av in
      let bt = mk_var_term bv in
         inf consts ((v,bt)::(u,at)::decls)
             (eqnlist_append_eqn eqs' a' (mk_prod_term at bt)) opt_eqs''
             ((av,Itt_void.top_term)::(bv,Itt_void.top_term)::defs') b

let resource typeinf += (spread_term, inf_spread)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two function types.
 *)
let resource sub +=
   (DSubtype ([<< a1:'A1 * 'B1['a1] >>, << a2:'A2 * 'B2['a2] >>;
               << 'A1 >>, << 'A2 >>;
               << 'B1['a1] >>, << 'B2['a1] >>],
              dT 0))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
