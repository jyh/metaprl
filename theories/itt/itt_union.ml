doc <:doc< 
   @begin[spelling]
   dT handedness inl inlFormation inr inrFormation reduceDecideInl
   reduceDecideInr selT
   @end[spelling]
  
   @begin[doc]
   @module[Itt_union]
  
   The union type $T_1 + T_2$ defines a union space containing the
   elements of both $T_1$ and $T_2$.  The union is @emph{disjoint}: the
   elements are @emph{tagged} with the @hrefterm[inl] and @hrefterm[inr]
   tags as belonging to the ``left'' type $T_1$ or the ``right'' type
   $T_2$.
  
   The union type is the first primitive type that can have more than one
   element.  The tag makes the handedness of membership decidable, and
   the union type $@unit + @unit$ contains two elements: <<inl{it}>> and
   <<inr{it}>>.  The @hrefmodule[Itt_bool] module uses this definition to
   define the Boolean values, where @emph{false} is <<inl{it}>> and
   @emph{true} is <<inr{it}>>.
  
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

open Printf
open Mp_debug
open String_set
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Mp_resource
open Unify_mm

open Var
open Tactic_type.Sequent
open Tactic_type.Tacticals

open Dtactic
open Top_conversionals

open Itt_equal
open Itt_struct
open Itt_subtype

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_union%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @terms
  
   The @tt{union} type is the binary union of two types $A$ and $B$.
   The elements are @inl{'a} for $a @in A$ and @inr{b} for $b @in B$.
   The @tt{decide} term @emph{decides} the handedness of the term $x @in A + B$.
   @end[doc]
>>
declare \union{'A; 'B}
declare inl{'x}
declare inr{'x}
declare decide{'x; y. 'a['y]; z. 'b['z]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rewrites
  
   The following two rules define the computational behavior of the
   @hrefterm[decide] term.  There are two reductions, the @tt{reduceDecideInl}
   rewrite describes reduction of @tt{decide} on the @hrefterm[inl] term,
   and @tt{reduceDecideInr} describes reduction on the @hrefterm[inr] term.
   The rewrites are added to the @hrefconv[reduceC] resource.
  
   @end[doc]
>>
prim_rw reduceDecideInl {| reduce |} : decide{inl{'x}; u. 'l['u]; v. 'r['v]} <--> 'l['x]
prim_rw reduceDecideInr {| reduce |} : decide{inr{'x}; u. 'l['u]; v. 'r['v]} <--> 'r['x]
doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_inl
prec prec_union

dform union_df : except_mode[src] :: parens :: "prec"[prec_union] :: \union{'A; 'B} =
   slot{'A} " " `"+" " " slot{'B}

dform inl_df : except_mode[src] :: parens :: "prec"[prec_inl] :: inl{'a} =
   `"inl" " " slot{'a}

dform inr_df : except_mode[src] :: parens :: "prec"[prec_inl] :: inr{'a} =
   `"inr" " " slot{'a}

dform decide_df : except_mode[src] :: decide{'x; y. 'a; z. 'b} =
   szone pushm[0] pushm[3] `"match" " " slot{'x} " " `"with" hspace
   `"inl " slot{'y} `" -> " slot{'a} popm hspace
   pushm[3] `"| inr " slot{'z} `" -> " slot{'b} popm popm ezone

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext A + B
 * by unionFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
prim unionFormation :
   ('A : sequent ['ext] { <H> >- univ[i:l] }) -->
   ('B : sequent ['ext] { <H> >- univ[i:l] }) -->
   sequent ['ext] { <H> >- univ[i:l] } =
   'A + 'B

doc <:doc< 
   @begin[doc]
   @rules
   @modsubsection{Typehood and equality}
  
   The equality of the @hrefterm[union] type is intensional; the
   union $A + B$ is a type if both $A$ and $B$ are types.
   @end[doc]
>>
prim unionEquality {| intro []; eqcd |} :
   [wf] sequent [squash] { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { <H> >- 'B1 = 'B2 in univ[i:l] } -->
   sequent ['ext] { <H> >- 'A1 + 'B1 = 'A2 + 'B2 in univ[i:l] } =
   it

(*
 * Typehood.
 *)
prim unionType {| intro [] |} :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- "type"{'B} } -->
   sequent ['ext] { <H> >- "type"{. 'A + 'B } } =
   it

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction}
  
   The union type $A + B$ is true if both $A$ and $B$ are types,
   and either 1) $A$ is provable, or 2) $B$ is provable.  The following
   two rules are added to the @hreftactic[dT] tactic.  The application
   uses the @hreftactic[selT] tactic to choose the handedness; the
   @tt{inlFormation} rule is applied with the tactic @tt{selT 1 (dT 0)}
   and the @tt{inrFormation} is applied with @tt{selT 2 (dT 0)}.
   @end[doc]
>>
prim inlFormation {| intro [SelectOption 1] |} :
   [main] ('a : sequent ['ext] { <H> >- 'A }) -->
   [wf] sequent [squash] { <H> >- "type"{'B} } -->
   sequent ['ext] { <H> >- 'A + 'B } =
   inl{'a}

(*
 * H >- A + B ext inl a
 * by inrFormation
 * H >- B
 * H >- A = A in Ui
 *)
prim inrFormation {| intro [SelectOption 2] |} :
   [main] ('b : sequent ['ext] { <H> >- 'B }) -->
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   sequent ['ext] { <H> >- 'A + 'B } =
   inr{'b}

doc <:doc< 
   @begin[doc]
   @modsubsection{Membership}
  
   The following two rules define membership, $@inl{a} @in A + B$
   if $a @in A$ and $@inr{b} @in A + B$ if $b @in B$.  Both
   $A$ and $B$ must be types.
   @end[doc]
>>
prim inlEquality {| intro []; eqcd |} :
   [wf] sequent [squash] { <H> >- 'a1 = 'a2 in 'A } -->
   [wf] sequent [squash] { <H> >- "type"{'B} } -->
   sequent ['ext] { <H> >- inl{'a1} = inl{'a2} in 'A + 'B } =
   it

(*
 * H >- inr b1 = inr b2 in A + B
 * by inrEquality
 * H >- b1 = b2 in B
 * H >- A = A in Ui
 *)
prim inrEquality {| intro []; eqcd |} :
   [wf] sequent [squash] { <H> >- 'b1 = 'b2 in 'B } -->
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   sequent ['ext] { <H> >- inr{'b1} = inr{'b2} in 'A + 'B } =
   it

doc <:doc< 
   @begin[doc]
   @modsubsection{Elimination}
  
   The handedness of the union membership is @emph{decidable}.  The
   elimination rule performs a case analysis in the assumption $x@colon A + B$;
   the first for the @tt{inl} case, and the second for the @tt{inr}.  The proof
   extract term is the @tt{decide} combinator (which performs a decision
   on element membership).
   @end[doc]
>>
prim unionElimination {| elim [ThinOption thinT] |} 'H :
   [left] ('left['u] : sequent ['ext] { <H>; 'A + 'B; u: 'A; <J[inl{'u}]> >- 'T[inl{'u}] }) -->
   [right] ('right['u] : sequent ['ext] { <H>; 'A + 'B; v: 'B; <J[inr{'v}]> >- 'T[inr{'v}] }) -->
   sequent ['ext] { <H>; x: 'A + 'B; <J['x]> >- 'T['x] } =
   decide{'x; u. 'left['u]; v. 'right['v]}

doc <:doc< 
   @begin[doc]
   @modsubsection{Combinator equality}
  
   The @tt{decide} term equality is true if there is @emph{some} type
   $A + B$ for which all the subterms are equal.
   @end[doc]
>>
prim decideEquality {| intro []; eqcd |} bind{z. 'T['z]} ('A + 'B) :
   [wf] sequent [squash] { <H> >- 'e1 = 'e2 in 'A + 'B } -->
   [wf] sequent [squash] { <H>; u: 'A; 'e1 = inl{'u} in 'A + 'B >- 'l1['u] = 'l2['u] in 'T[inl{'u}] } -->
   [wf] sequent [squash] { <H>; v: 'B; 'e1 = inr{'v} in 'A + 'B >- 'r1['v] = 'r2['v] in 'T[inr{'v}] } -->
   sequent ['ext] { <H> >- decide{'e1; u1. 'l1['u1]; v1. 'r1['v1]} =
                   decide{'e2; u2. 'l2['u2]; v2. 'r2['v2]} in
                   'T['e1] } =
   it

doc <:doc< 
   @begin[doc]
   @modsubsection{Subtyping}
  
   The union type $A_1 + A_2$ is a subtype of type $A_2 + B_2$ if
   $A_1 @subseteq A_2$ and $B_1 @subseteq B_2$.
   @end[doc]
>>
prim unionSubtype {| intro [] |} :
   ["subtype"] sequent [squash] { <H> >- 'A1 subtype 'A2 } -->
   ["subtype"] sequent [squash] { <H> >- 'B1 subtype 'B2 } -->
   sequent ['ext] { <H> >- 'A1 + 'B1 subtype 'A2 + 'B2  } =
   it
doc <:doc< @docoff >>

(*
 * Interactive.
 *)
interactive unionContradiction1 {| elim [] |} 'H :
   sequent ['ext] { <H>; x: inl{'y} = inr{'z} in 'A+'B; <J['x]> >- 'C['x] }

interactive unionContradiction2 {| elim [] |} 'H :
   sequent ['ext] { <H>; x: inr{'y} = inl{'z} in 'A+'B; <J['x]> >- 'C['x] }

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let union_term = << 'A + 'B >>
let union_opname = opname_of_term union_term
let is_union_term = is_dep0_dep0_term union_opname
let dest_union = dest_dep0_dep0_term union_opname
let mk_union_term = mk_dep0_dep0_term union_opname

let inl_term = << inl{'x} >>
let inl_opname = opname_of_term inl_term
let is_inl_term = is_dep0_term inl_opname
let dest_inl = dest_dep0_term inl_opname
let mk_inl_term = mk_dep0_term inl_opname

let inr_term = << inr{'x} >>
let inr_opname = opname_of_term inr_term
let is_inr_term = is_dep0_term inr_opname
let dest_inr = dest_dep0_term inr_opname
let mk_inr_term = mk_dep0_term inr_opname

let decide_term = << decide{'x; y. 'a['y]; z. 'b['z]} >>
let decide_opname = opname_of_term decide_term
let is_decide_term = is_dep0_dep1_dep1_term decide_opname
let dest_decide = dest_dep0_dep1_dep1_term decide_opname
let mk_decide_term = mk_dep0_dep1_dep1_term decide_opname

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (union_term, infer_univ_dep0_dep0 dest_union)

(*
 * Type of inl.
 *)
let inf_inl inf consts decls eqs opt_eqs defs t =
   let a = dest_inl t in
   let eqs', opt_eqs', defs', a' = inf consts decls eqs opt_eqs defs a in
   let b = Typeinf.vnewname consts defs' "T-r" in
       eqs', opt_eqs', ((b,<<void>>)::defs') , mk_union_term a' (mk_var_term b)

let resource typeinf += (inl_term, inf_inl)

(*
 * Type of inr.
 *)
let inf_inr inf consts decls eqs opt_eqs defs t =
   let a = dest_inl t in
   let eqs', opt_eqs', defs', a' = inf consts decls eqs opt_eqs defs a in
   let b = Typeinf.vnewname consts defs' "T-l" in
       eqs', opt_eqs', ((b,<<void>>)::defs') , mk_union_term (mk_var_term b) a'

let resource typeinf += (inr_term, inf_inr)

(*
 * Type of decide.
 *)
let inf_decide inf consts decls eqs opt_eqs defs t =
   let e, x, a, y, b = dest_decide t in
   let eqs', opt_eqs', defs', e' = inf consts decls eqs opt_eqs defs e in
   let consts = StringSet.add (StringSet.add consts x) y in
   let l = Typeinf.vnewname consts defs' "T-l" in
   let l' = mk_var_term l in
   let r = Typeinf.vnewname consts defs' "T-r" in
   let r' = mk_var_term r in
   let eqs'', opt_eqs'', defs'', a' =
      inf consts ((x, l')::decls)
          (eqnlist_append_eqn eqs' e' (mk_union_term l' r')) opt_eqs'
          ((l,<<top>>)::(r,<<top>>)::defs') a
   in
   let eqs''', opt_eqs''', defs''', b' =
      inf consts ((y, r')::decls) eqs'' opt_eqs'' defs'' b
   in eqs''', ((a',b')::opt_eqs'''), defs''', a'

let resource typeinf += (decide_term, inf_decide)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two union types.
 *)
let resource sub +=
   (DSubtype ([<< 'A1 + 'B1 >>, << 'A2 + 'B2 >>;
               << 'A1 >>, << 'A2 >>;
               << 'B1 >>, << 'B2 >>],
              dT 0))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)


