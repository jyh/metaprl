(*!
 * @spelling{rfun rfunctionFormation}
 *
 * @begin[doc]
 * @theory[Itt_rfun]
 *
 * The @tt{Itt_rfun} module defines the @emph{very-dependent function
 * type}.  This is the root type for the function types
 * for the dependent-function @hreftheory[Itt_dfun] and
 * the nondependent-function @hreftheory[Itt_fun].
 *
 * A complete description of the semantics of the type is given
 * in Section @reftheory["issues-rfun"].  The type can be described
 * informally as follows.
 * The syntax of the type is $@rfun{f; x; A; B[f, x]}$.
 * The term $f$ represents the functions $f$ that are members of
 * the type, the term $A$ is the type of the @emph{domain}, and
 * given any particular function $f$ in the type, and any argument
 * $x @in A$, the type of the function @emph{value} is the type
 * $B[f, x]$.  Roughly speaking, a function $g$ is in the
 * type $@rfun{f; x; A; B[f, x]}$ if $g(x)$ has type $B[g, x]$ for
 * any element $x @in A$.  In addition, the domain $A$ must be
 * well-founded with a partial order on $A$, and the type $B[f, x]$
 * must be well-formed if $f$ is restricted to arguments smaller
 * the $x$.
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
include Itt_void
include Itt_set
include Itt_struct
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
open Base_dtactic

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent

open Itt_void
open Itt_equal
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_rfun%t"

(* debug_string DebugLoad "Loading itt_rfun..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The @tt{rfun} type defines the very-dependent function $@rfun{f; x; A; B}$;
 * the @tt{fun} type is used to define dependent functions $@fun{x; A; B[x]}$ and
 * nondependent functions $@fun{A; B}$.
 *
 * The elements of the function types are
 * the functions $@lambda{x; b[x]}$, and the induction combinator is the
 * application $@apply{f; a}$.  The @tt{fix} term defines a @emph{fixpoint}.
 *
 * The @tt{well_founded} terms are used to define the well-founded order
 * on the domain; the definition is given with the well-founded rules below.
 * @end[doc]
 *)

declare "fun"{'A; 'B}
declare "fun"{'A; x. 'B['x]}
declare rfun{'A; f, x. 'B['f; 'x]}

declare lambda{x. 'b['x]}
declare apply{'f; 'a}

declare well_founded{'A; x, y. 'R['x; 'y]}
declare well_founded_assum{'A; a1, a2. 'R['a1; 'a2]; 'P}
declare well_founded_prop{'A}
declare well_founded_apply{'P; 'a}
declare fix{f. 'b['f]}
(*! @docoff *)

(*
 * Primitives.
 *)
let rfun_term = << { f | x: 'A -> 'B['f; 'x] } >>
let rfun_opname = opname_of_term rfun_term
let is_rfun_term = is_dep0_dep2_term rfun_opname
let dest_rfun = dest_dep0_dep2_term rfun_opname
let mk_rfun_term = mk_dep0_dep2_term rfun_opname

let well_founded_term = << well_founded{'A; x, y. 'R['x; 'y]} >>
let well_founded_opname = opname_of_term well_founded_term
let is_well_founded_term = is_dep0_dep2_term well_founded_opname
let dest_well_founded = dest_dep0_dep2_term well_founded_opname
let mk_well_founded_term = mk_dep0_dep2_term well_founded_opname

let lambda_term = << lambda{x. 'b['x]} >>
let lambda_opname = opname_of_term lambda_term
let is_lambda_term = is_dep1_term lambda_opname
let dest_lambda = dest_dep1_term lambda_opname
let mk_lambda_term = mk_dep1_term lambda_opname

let fix_term = << fix{x. 'b['x]} >>
let fix_opname = opname_of_term fix_term
let is_fix_term = is_dep1_term fix_opname
let dest_fix = dest_dep1_term fix_opname
let mk_fix_term = mk_dep1_term fix_opname

let apply_term = << apply{'f; 'a} >>
let apply_opname = opname_of_term apply_term
let is_apply_term = is_dep0_dep0_term apply_opname
let dest_apply = dest_dep0_dep0_term apply_opname
let mk_apply_term = mk_dep0_dep0_term apply_opname

let dfun_term = << x: 'A -> 'B['x] >>
let dfun_opname = opname_of_term dfun_term
let is_dfun_term = is_dep0_dep1_term dfun_opname
let dest_dfun = dest_dep0_dep1_term dfun_opname
let mk_dfun_term = mk_dep0_dep1_term dfun_opname

let fun_term = << 'A -> 'B >>
let fun_opname = opname_of_term fun_term
let is_fun_term = is_dep0_dep0_term fun_opname
let dest_fun = dest_dep0_dep0_term fun_opname
let mk_fun_term = mk_dep0_dep0_term fun_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_fun
prec prec_apply
prec prec_lambda
prec prec_lambda < prec_apply
prec prec_fun < prec_apply
prec prec_fun < prec_lambda

dform fun_df1 : parens :: "prec"[prec_fun] :: "fun"{'A; 'B} =
   slot["le"]{'A} " " rightarrow " " slot["lt"]{'B}

dform fun_df2 : parens :: "prec"[prec_fun] :: "fun"{'A; x. 'B} =
   slot{bvar{'x}} `":" slot{'A} " " rightarrow " " slot{'B}

dform fun_df3 : rfun{'A; f, x. 'B} =
   "{" " " slot{bvar{'f}} `" | "  "fun"{'A; x. 'B} `" }"

dform apply_df1 : parens :: "prec"[prec_apply] :: apply{'f; 'a} =
   slot["lt"]{'f} " " slot["le"]{'a}

dform lambda_df1 : parens :: "prec"[prec_lambda] :: lambda{x. 'b} =
   Nuprl_font!lambda slot{'x} `"." slot{'b}

dform fix_df1 : except_mode[src] :: fix{f. 'b} =
   `"fix" `"(" slot{'f} `"." slot{'b} `")"

dform well_founded_prop_df : except_mode[src] :: well_founded_prop{'A} =
   `"WellFounded " slot{'A} " " rightarrow `" Prop"

dform well_founded_apply_df : except_mode[src] :: well_founded_apply{'P; 'a} =
   slot{'P} `"[" slot{'a} `"]"

dform well_founded_assum_df : except_mode[src] :: well_founded_assum{'A; a1, a2. 'R; 'P} =
   szone pushm[3] `"WellFounded " Nuprl_font!forall slot{'a2} `":" slot{'A} `"."
   `"(" Nuprl_font!forall slot{'a1} `":" slot{'A} `". " slot{'R} " " Rightarrow well_founded_apply{'P; 'a1} `")"
   Rightarrow well_founded_apply{'P; 'a2} popm ezone

dform well_founded_df : except_mode[src] :: well_founded{'A; a, b. 'R} =
   szone pushm[3] `"WellFounded " slot{'a} `"," slot{'b} `":" slot{'A} `"." slot{'R} popm ezone

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The @tt{reduce_beta} rewrite defines normal beta-reduction.
 * The @tt{reduce_fix} rewrite defines reduction on the fixpoint
 * combinator.  The @tt{reduce_fix} rewrite can be derived by defining
 * the $Y$-combinator $Y @equiv @lambda f. @lambda x. (f@space (x@space x))@space (f@space (x@space x))$
 * and defining $@fix{x; b[x]} @equiv Y@space (@lambda{x; b[x]})$.
 * @end[doc]
 *)
prim_rw reduce_beta : (lambda{v. 'b['v]} 'a) <--> 'b['a]
prim_rw reduce_fix : fix{f. 'b['f]} <--> 'b[fix{f. 'b['f]}]
(*! @docoff *)

let resource reduce +=
   [<< (lambda{v. 'b['v]} 'a) >>, reduce_beta;
    << fix{f. 'b['f]} >>, reduce_fix]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @thysubsection{Well-foundness}
 *
 * The following three rules are used to define a well-founded order.
 * The term @hrefterm[well_founded_prop] $@"well_founded_prop"{A}$ represents an arbitrary
 * proposition (predicate) on $A$; the @hrefterm[well_founded_apply] $@"well_founded_apply"{P; a}$
 * represents the application of the proposition $P$ to $a$.  The @hrefterm[well_founded_assum]
 * term $@"well_founded_assum"{A; a_1; a_2; R[a_1, a_2]; P}$ asserts that predicate $P$ holds on
 * all elements of $a$ by induction on the relation $R[a_1, a_2]$.
 *
 * The reason this definition is so convoluted is that the definition of
 * well-foundness must be give @emph{before} defining functions and application.
 * The @hreftheory[Itt_well_founded] module provides simplified definitions
 * of well-foundness.
 * @end[doc]
 *)
prim well_founded_assum_elim {| elim_resource [ThinOption thinT] |} 'H 'J 'a 'a3 'u :
   [main] sequent [squash] { 'H; p: well_founded_assum{'A; a1, a2. 'R['a1; 'a2]; 'P}; 'J['p] >- 'a IN 'A } -->
   [main] sequent [squash] { 'H; p: well_founded_assum{'A; a1, a2. 'R['a1; 'a2]; 'P}; 'J['p]; a3: 'A; u: 'R['a3; 'a] >- well_founded_apply{'P; 'a3} } -->
   [main] ('t['u] : sequent [squash] { 'H; p: well_founded_assum{'A; a1, a2. 'R['a1; 'a2]; 'P}; 'J['p]; u: well_founded_apply{'P; 'a} >- 'C['p] }) -->
   sequent ['ext] { 'H; p: well_founded_assum{'A; a1, a2. 'R['a1; 'a2]; 'P}; 'J['p] >- 'C['p] } =
   't[it]

prim well_founded {| intro_resource [] |} 'H 'a1 'a2 'a3 'u 'v 'p 'P :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; a1: 'A; a2: 'A >- "type"{'R['a1; 'a2]} } -->
   [main] sequent [squash] { 'H; a1: 'A; u: 'R['a1; 'a1] >- void } -->
   [main] sequent [squash] { 'H; a1: 'A; a2: 'A; u: 'R['a1; 'a2]; v: 'R['a2; 'a1] >- void } -->
   [main] sequent [squash] { 'H; a1: 'A; a2: 'A; a3: 'A; u: 'R['a1; 'a2]; v: 'R['a2; 'a3] >- 'R['a1; 'a3] } -->
   [main] sequent [squash] { 'H; a1: 'A; P: well_founded_prop{'A}; p: well_founded_assum{'A; a2, a3. 'R['a2; 'a3]; 'P} >- well_founded_apply{'P; 'a1} } -->
   sequent ['ext] { 'H >- well_founded{'A; a, b. 'R['a; 'b]} } =
   it

prim well_founded_apply_type {| intro_resource [] |} 'H 'A :
   [wf] sequent [squash] { 'H >- 'P IN well_founded_prop{'A} } -->
   [wf] sequent [squash] { 'H >- 'A IN univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'a IN 'A } -->
   sequent ['ext] { 'H >- well_founded_apply{'P; 'a} IN univ[i:l] } =
   it

(*!
 * @docoff
 *)
prim rfunctionFormation 'H { f | a: 'A -> 'B['f; 'a] } :
   [wf] sequent [squash] { 'H >- { f | a: 'A -> 'B['f; 'a] } = { f | a: 'A -> 'B['f; 'a] } in univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] } =
   { f | a: 'A -> 'B['f; 'a] }

(*!
 * @begin[doc]
 * @thysubsection{Typehood and equality}
 *
 * The well-formedness of the very-dependent function
 * requires that the domain type $A$ be a type, the the domain
 * be well-founded with some relation $R$, and that $B[f, x]$ be
 * a type for any restricted function $@rfun{f; y; @set{A; x; R[z, y]}; B[f, y]}$.
 * @end[doc]
 *)
prim rfunctionEquality  {| intro_resource []; eqcd_resource |} 'H lambda{a. lambda{b. 'R['a; 'b]}} 'g 'y 'z :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- well_founded{'A1; a, b. 'R['a; 'b]} } -->
   [wf] sequent [squash] { 'H;
             y: 'A1;
             g: { f1 | x1: { z: 'A1 | 'R['z; 'y] } -> 'B1['f1; 'x1] }
             >- 'B1['g; 'y] = 'B2['g; 'y] in univ[i:l]
           } -->
   sequent ['ext] { 'H >- { f1 | a1:'A1 -> 'B1['f1; 'a1] }
                   = { f2 | a2:'A2 -> 'B2['f2; 'a2] }
                   in univ[i:l]
           } =
   it

prim rfunctionType  {| intro_resource [] |} 'H lambda{a. lambda{b. 'R['a; 'b]}} 'g 'y 'z :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- well_founded{'A; a, b. 'R['a; 'b]} } -->
   [wf] sequent [squash] { 'H;
             y: 'A;
             g: { f | x: { z: 'A | 'R['z; 'y] } -> 'B['f; 'x] }
             >- "type"{'B['g; 'y]}
           } -->
   sequent ['ext] { 'H >- "type"{. { f | a:'A -> 'B['f; 'a] } } } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Introduction}
 *
 * Viewed as a proposition, the very-dependent function type
 * represents a @emph{recursive} proposition.  The function type
 * $@rfun{f; x; A; B[f, x]}$ must be well-formed with well-founded
 * order $R$ on $A$, and $B[f, x]$ must be true for each $B[g, y]$
 * for $y @in A$ and $g$ a function in the restricted function space
 * $@rfun{f; x; @set{A; z; R[z, y]}; B[f, x]}$ (the induction
 * hypothesis).  The proof extract term contains a fixpoint, due to
 * the induction.  The fixpoint is guaranteed to terminate
 * because the domain is well-founded.
 * @end[doc]
 *)
prim rfunction_lambdaFormation {| intro_resource [] |} 'H lambda{a. lambda{b. 'R['a; 'b]}} 'g 'y 'z :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- well_founded{'A; a, b. 'R['a; 'b]} } -->
   ('b['g; 'y] : sequent ['ext] { 'H; y: 'A; g: { f | x: { z: 'A | 'R['z; 'y] } -> 'B['f; 'x] } >- 'B['g; 'y] }) -->
   sequent ['ext] { 'H >- { f | x:'A -> 'B['f; 'x] } } =
   lambda{y. fix{g. 'b['g; 'y]}}

(*!
 * @begin[doc]
 * @thysubsection{Membership}
 *
 * The members of the function space are the @hrefterm[lambda] terms.
 * The function space must be well-formed, and the body of the function
 * must inhabit the range type $B$ where the @tt{lambda} function is
 * substituted for the function argument.
 * @end[doc]
 *)
prim rfunction_lambdaEquality {| intro_resource []; eqcd_resource |} 'H 'y :
   [wf] sequent [squash] { 'H >- "type"{{ f | x: 'A -> 'B['f; 'x] }} } -->
   [wf] sequent [squash] { 'H; y: 'A >- 'b1['y] = 'b2['y] in 'B[lambda{x1. 'b1['x1]}; 'y] } -->
   sequent ['ext] { 'H >- lambda{x1. 'b1['x1]} = lambda{x2. 'b2['x2]} in { f | x: 'A -> 'B['f; 'x] } } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Extensional equality}
 *
 * The function space is one of the few types in the @Nuprl type
 * theory with an @emph{extensional} equality.  Normally, equality is
 * intensional --- it depends on the syntactic structure of the the
 * terms in the type.  The function space allows equality of functions
 * $f_1$ and $f_2$ if their @emph{application} provides equal values on
 * equal arguments.  The functions and the function type must all be
 * well-formed (and in fact, this implicitly requires that $f_1$ and
 * $f_2$ both be @tt{lambda} terms).
 * @end[doc]
 *)
prim rfunctionExtensionality 'H
        ({ g1 | x1:'A1 -> 'B1['g1; 'x1] })
        ({ g2 | x2:'A2 -> 'B2['g2; 'x2] })
        'y :
   [wf] sequent [squash] { 'H >- "type"{{ g | x:'A -> 'B['g; 'x] }} } -->
   [main] sequent [squash] { 'H; y: 'A >- 'f1 'y = 'f2 'y in 'B['f1; 'y] } -->
   [wf] sequent [squash] { 'H >- 'f1 IN { g1 | x1:'A1 -> 'B1['g1; 'x1] } } -->
   [wf] sequent [squash] { 'H >- 'f2 IN { g2 | x2:'A2 -> 'B2['g2; 'x2] } } -->
   sequent ['ext] { 'H >- 'f1 = 'f2 in { g | x:'A -> 'B['g; 'x] } } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Elimination}
 *
 * The elimination form for a function type $f@colon @rfun{g; x; A; B[g, x]}$
 * allows @emph{instantiation} of the function on an argument $a$, to
 * get a proof $B[f, a]$.
 * @end[doc]
 *)
prim rfunctionElimination {| elim_resource [] |} 'H 'J 'f 'a 'y 'v :
   [wf] sequent [squash] { 'H; f: { g | x:'A -> 'B['g; 'x] }; 'J['f] >- 'a IN 'A } -->
   ('t['f; 'y; 'v] : sequent ['ext] { 'H;
                               f: { g | x:'A -> 'B['g; 'x] };
                               'J['f];
                               y: 'B['f; 'a];
                               v: 'y = 'f 'a in 'B['f; 'a]
                               >- 'T['f] }) -->
   sequent ['ext] { 'H; f: { g | x:'A -> 'B['g; 'x] }; 'J['f] >- 'T['f] } =
   't['f; 'f 'a; it]

(*!
 * @begin[doc]
 * @thysubsection{Combinator equality}
 *
 * Two @emph{applications} are equal if their functions are equal,
 * and their arguments are equal.
 * @end[doc]
 *)
prim rfunction_applyEquality {| eqcd_resource |} 'H ({ f | x:'A -> 'B['f; 'x] }) :
   [wf] sequent [squash] { 'H >- 'f1 = 'f2 in { f | x:'A -> 'B['f; 'x] } } -->
   [wf] sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- 'f1 'a1 = 'f2 'a2 in 'B['f1; 'a1] } =
   it
(*! @docoff *)

let rfunction_applyEquality' t p =
   rfunction_applyEquality (Sequent.hyp_count_addr p) t p

(*!
 * @begin[doc]
 * @thysubsection{Subtyping}
 *
 * Function subtyping is @emph{contravariant} in the domain and
 * @emph{covariant} in the range.  The range subtyping is given using
 * an arbitrary instance $f$ in the function space.
 * @end[doc]
 *)
interactive rfunction_rfunction_subtype {| intro_resource [] |} 'H 'a 'f lambda{a. lambda{b. 'R['a; 'b]}} :
   [main] sequent [squash] { 'H >- subtype{'A2; 'A1} } -->
   [wf] sequent [squash] { 'H >- "type"{.{f1 | x1: 'A1 -> 'B1['f1; 'x1] }} } -->
   [wf] sequent [squash] { 'H >- "type"{.{f2 | x2: 'A2 -> 'B2['f2; 'x2] }} } -->
   [wf] sequent [squash] { 'H; a1: 'A1; a2: 'A1 >- "type"{'R['a1; 'a2]} } -->
   [main] sequent [squash] { 'H; f: {f1 | x1: 'A1 -> 'B1['f1; 'x1]}; a: 'A2 >-
                          subtype{'B1['f; 'a]; 'B2['f; 'a]}
                    } -->
   sequent ['ext] { 'H >- subtype{.{ f1 | x1: 'A1 -> 'B1['f1; 'x1] }; .{ f2 | x2: 'A2 -> 'B2['f2; 'x2] } } }
(*! @docoff *)

(************************************************************************
 * D TACTIC                                                             *
 ************************************************************************)

(*
 * We handle extensionality explicitly.
 *)
let rfunction_extensionalityT t1 t2 p =
   let t, _, _ = dest_equal (Sequent.concl p) in
   let _, v, _, _ = dest_rfun t in
   let v = maybe_new_vars1 p v in
      rfunctionExtensionality (Sequent.hyp_count_addr p) t1 t2 v p

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of rfun.
 *)
let inf_rfun inf consts decls eqs opt_eqs defs t =
   let f, v, a, b = dest_rfun t in
   infer_univ_dep0_dep1
      (fun _ -> v,a,b) inf (StringSet.add f consts) ((f,t)::decls) eqs opt_eqs defs t

let resource typeinf += (rfun_term, inf_rfun)

(*
 * Type of lambda.
 *)
let inf_lambda inf consts decls eqs opt_eqs defs t =
   let v, b = dest_lambda t in
   let consts = StringSet.add v consts in
   let a = Typeinf.vnewname consts defs "T" in
   let a' = mk_var_term a in
   let eqs', opt_eqs', defs', b' =
      inf consts ((v, a')::decls) eqs opt_eqs ((a,<<top>>)::defs) b
   in
      eqs', opt_eqs', defs', mk_dfun_term v a' b'

let resource typeinf += (lambda_term, inf_lambda)

(*
 * Type of apply.
 *)
let inf_apply inf consts decls eqs opt_eqs defs t =
   let f, a = dest_apply t in
   let eqs', opt_eqs', defs', f' = inf consts decls eqs opt_eqs defs f in
   let eqs'', opt_eqs'', defs'', a' = inf consts decls eqs' opt_eqs' defs' a in
   let eqs''', opt_eqs''', _ , f'' =
      Typeinf.typeinf_final consts eqs'' opt_eqs'' defs'' f' in
   if is_dfun_term f'' then
      let v, d, r = dest_dfun f'' in
         eqs''', opt_eqs''', defs'', subst1 r v a
   else if is_rfun_term f'' then
      let f''', v, d, r = dest_rfun f'' in
         eqs''', opt_eqs''', defs'', subst r [f'''; v] [f; a]
   else
      let av = Typeinf.vnewname consts defs'' "A" in
      let bv = Typeinf.vnewname consts defs'' "B" in
      let at = mk_var_term av in
      let bt = mk_var_term bv in
         (eqnlist_append_eqn eqs'' f' (mk_fun_term at bt)),((a',at)::opt_eqs'''),
         ((av, <<top>>)::(bv,<<void>>)::defs''), bt

let resource typeinf += (apply_term, inf_apply)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
