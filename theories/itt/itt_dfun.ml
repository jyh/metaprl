(*!
 * @spelling{dfun}
 *
 * @begin[doc]
 * @theory[Itt_dfun]
 *
 * The @tt{Itt_dfun} module is @emph{derived} from the
 * @hreftheory[Itt_rfun] module.  The type $@fun{x; A; B[x]}$ is
 * equivalent to the type $@rfun{f; x; A; B[x]}$, where $f$ is
 * not bound in $B[x]$.  The @emph{well-founded} restriction in
 * for the very-dependent function type is always trivially satisfied
 * (since the range type $B[x]$ never invokes $f$).
 * The @tt{Itt_dfun} module derives the dependent-function
 * rules.
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
include Itt_rfun
include Itt_struct
include Itt_void
include Itt_unit
(*! @docoff *)

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Var
open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Base_dtactic

open Itt_equal
open Itt_subtype
open Itt_rfun
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_dfun%t"


(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The @tt{unfold_dfun} gives the definition of the
 * dependent-function space.
 * @end[doc]
 *)
prim_rw unfold_dfun : (x: 'A -> 'B['x]) <--> ({ f | x: 'A -> 'B['x] })

(*!
 * @begin[doc]
 *
 * The @tt{reduceEta} rewrite defines eta-reduction.
 * This is conditional reduction: one can apply it only for functions.
 * @end[doc]
 *)

 prim_rw reduceEta (x: 'A -> 'B['x]) :
   ('f IN (x: 'A -> 'B['x])) -->
    lambda{x. 'f 'x} <--> 'f


(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Lemmas}
 *
 * The @tt{void_well_founded} rule is a lemma that is
 * useful for proving the well-formedness of the
 * dependent-function space.  The @hrefterm[void]
 * type is trivially well-founded, since it has no elements.
 * @end[doc]
 *)
interactive void_well_founded {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- well_founded{'A; a1, a2. void} }

(*
 * @begin[doc]
 * @thysubsection{Typehood and equality}
 *
 * The dependent-function space retains the intensional type
 * equality of the very-dependent type.
 * @end[doc]
 *)
interactive functionEquality {| intro_resource []; eqcd_resource |} 'H 'x :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H; x: 'A1 >- 'B1['x] = 'B2['x] in univ[i:l] } -->
   sequent ['ext] { 'H >- (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l] }

(*
 * Typehood.
 *)
interactive functionType {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'A1} } -->
   [wf] sequent [squash] { 'H; x: 'A1 >- "type"{'B1['x]} } -->
   sequent ['ext] { 'H >- "type"{. a1:'A1 -> 'B1['a1] } }

(*!
 * @begin[doc]
 * @thysubsection{Introduction}
 *
 * The propositional interpretation of the dependent-function
 * is the universal quantification @hrefterm[all], $@all{a; A; B[x]}$.  The
 * universal quantification is true, if it is a type,
 * and $B[a]$ is true for any $a @in A$.
 * @end[doc]
 *)
interactive lambdaFormation {| intro_resource [] |} 'H 'z :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [main] ('b['z] : sequent ['ext] { 'H; z: 'A >- 'B['z] }) -->
   sequent ['ext] { 'H >- a:'A -> 'B['a] }

(*!
 * @begin[doc]
 * @thysubsection{Membership}
 *
 * The dependent function space contains the @hrefterm[lambda] functions.
 * @end[doc]
 *)
interactive lambdaEquality {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; x: 'A >- 'b1['x] = 'b2['x] in 'B['x] } -->
   sequent ['ext] { 'H >- lambda{a1. 'b1['a1]} = lambda{a2. 'b2['a2]} in a:'A -> 'B['a] }

(*!
 * @begin[doc]
 * @thysubsection{Extensionality}
 *
 * The dependent-function retains the extensional membership
 * equality of the very-dependent function type.  This rule is
 * derived from the @hrefrule[rfunctionExtensionality] rule.
 * @end[doc]
 *)
interactive functionExtensionality 'H (y:'C -> 'D['y]) (z:'E -> 'F['z]) 'u :
   [main] sequent [squash] { 'H; u: 'A >- ('f 'u) = ('g 'u) in 'B['u] } -->
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'f = 'f in y:'C -> 'D['y] } -->
   [wf] sequent [squash] { 'H >- 'g = 'g in z:'E -> 'F['z] } -->
   sequent ['ext] { 'H >- 'f = 'g in x:'A -> 'B['x] }

(*!
 * @begin[doc]
 * @thysubsection{Elimination}
 *
 * The elimination rule @emph{instantiates} the function
 * $f@colon @fun{x; A; B[x]}$ with an argument $a @in A$, to
 * obtain a proof of $B[a]$.
 * @end[doc]
 *)
interactive functionElimination {| elim_resource [] |} 'H 'J 'f 'a 'y 'v :
   [wf] sequent [squash] { 'H; f: x:'A -> 'B['x]; 'J['f] >- 'a IN 'A } -->
   ('t['f; 'y; 'v] : sequent ['ext] { 'H; f: x:'A -> 'B['x]; 'J['f]; y: 'B['a]; v: 'y = ('f 'a) in 'B['a] >- 'T['f] }) -->
   sequent ['ext] { 'H; f: x:'A -> 'B['x]; 'J['f] >- 'T['f] }

(*!
 * @begin[doc]
 * @thysubsection{Combinator equality}
 *
 * Applications have (at least) an @emph{intensional} equality; they are
 * equal if their functions and arguments are equal.
 * @end[doc]
 *)
interactive applyEquality {| eqcd_resource |} 'H (x:'A -> 'B['x]) :
   sequent [squash] { 'H >- 'f1 = 'f2 in x:'A -> 'B['x] } -->
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- ('f1 'a1) = ('f2 'a2) in 'B['a1] }

let applyEquality' t p =
   applyEquality (Sequent.hyp_count_addr p) t p

(*!
 * @begin[doc]
 * @thysubsection{Subtyping}
 *
 * Function spaces are @emph{contravariant} in the domains, and
 * @emph{covariant} in their ranges.  More specifically, the
 * ranges must be pointwise covariant.
 *
 * @end[doc]
 *)
interactive functionSubtype {| intro_resource [] |} 'H 'a :
   sequent [squash] { 'H >- subtype{'A2; 'A1} } -->
   sequent [squash] { 'H; a: 'A1 >- subtype{'B1['a]; 'B2['a]} } -->
   sequent ['prop] { 'H >- subtype{ (a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2]) } }
(*! @docoff *)

(*
(*
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; J[x] >- T[x]
 * by function_subtypeElimination i
 *
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; y: A2 <= A1; z: a:A2 -> B2[a] <= B1[a]; J[x] >- T[x]
 *)
interactive function_subtypeElimination {| elim_resource [] |} 'H 'J 'x 'y 'z 'a :
   ('t['x; 'y; 'z] : sequent ['ext] { 'H;
             x: subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])};
             'J['x];
             y: subtype{'A2; 'A1};
             z: a:'A2 -> subtype{'B1['a]; 'B2['a]}
             >- 'T['x]
           }) -->
   sequent ['ext] { 'H; x: subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])}; 'J['x] >- 'T['x] }
*)

(*
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; J[x] >- T[x]
 * by function_equalityElimination
 *
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; y: A1 = A2 in Ui; z: a:A1 -> B1[a] = B2[a] in Ui; J[x] >- T[x]
interactive function_equalityElimination {| elim_resource [ThinOption thinT] |} 'H 'J 'x 'y 'z 'a :
   ('t['x; 'y; 'z] : sequent { 'H;
             x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l];
             'J['x];
             y: 'A1 = 'A2 in univ[i:l];
             z: a:'A1 -> ('B1['a] = 'B2['a] in univ[i:l])
             >- 'T['x]
           }) -->
   sequent { 'H; x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l]; 'J['x] >- 'T['x] }
 *)

(*
 * H >- Ui ext a:A -> B
 * by functionFormation a A
 *
 * H >- A = A in Ui
 * H, a: A >- Ui ext B
 *)
interactive functionFormation 'H 'a 'A :
   [wf] sequent [squash] { 'H >- 'A IN univ[i:l] } -->
   ('B['a] : sequent ['ext] { 'H; a: 'A >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] }

(************************************************************************
 * EXTENSIOANLITY                                                       *
 ************************************************************************)

(*
 * Takes two arguments.
 *)
let dfun_extensionalityT t1 t2 p =
   let t, _, _ = dest_equal (Sequent.concl p) in
   let v, _, _ = dest_dfun t in
   let v = maybe_new_vars1 p v in
      functionExtensionality (Sequent.hyp_count_addr p) t1 t2 v p

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (dfun_term, infer_univ_dep0_dep1 dest_dfun)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two function types.
 *)
let dfun_subtypeT p =
   let a = get_opt_var_arg "x" p in
      (functionSubtype (Sequent.hyp_count_addr p) a
       thenT addHiddenLabelT "subtype") p

let resource sub +=
   (DSubtype ([<< a1:'A1 -> 'B1['a1] >>, << a2:'A2 -> 'B2['a2] >>;
               << 'A2 >>, << 'A1 >>;
               << 'B1['a1] >>, << 'B2['a1] >>],
              dfun_subtypeT))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
