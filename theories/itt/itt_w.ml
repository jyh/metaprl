(*!
 * @begin[doc]
 * @module[Itt_w]
 *
 * The @tt{Itt_w} module defines the recursive @i{W}-type.
 * The @i{W} type has the form $@w{x; A; B[x]}$, where
 * $A$ is a type, and $B[a]$ is a family of types indexed by
 * $a @in A$.
 *
 * The elements of the @i{W}-type are the nodes $@tree{a; f}$,
 * where $a @in A$, and $f$ is a function with domain $B[a]$ that produces
 * the ``children'' of the node.  The children also inhabit the
 * @i{W}-type, and $f$ is required to have type
 * $B[a] @rightarrow @w{x; A; B[x]}$.
 *
 * The @i{W}-type is defined as primitive.  It @emph{can}
 * be derived from the recursive type @hrefmodule[Itt_srec], with
 * the definition:
 *
 * $$@w{x; A; B[x]} @equiv @srec{T; @prod{x; A; @fun{B[a]; T}}}.$$
 *
 * However, the $W$ type has a simpler semantics than the recursive
 * type.  We keep it as primitive so that the recursive type can
 * be omitted if the semantics are questionable.
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
extends Itt_equal
extends Itt_rfun
extends Itt_struct
extends Itt_struct2
extends Itt_inv_typing
(*! @docoff *)

open Opname
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Var

open Base_dtactic

open Itt_equal
open Itt_struct

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The $W$ type is type of trees, $W = @prod{a; A; @fun{B[a]; W}}$.
 * @end[doc]
 *)
declare w{'A; x. 'B['x]}

(*!
 * @begin[doc]
 * The @tt{tree} terms inhabit the $W$-type.
 * Each node has a label $a @in A$, and a function $f$ with
 * domain $B[a]$ to compute the children of the node.
 * @end[doc]
 *)
declare tree{'a; 'f}

(*!
 * @begin[doc]
 * The @tt[tree_ind] term is the induction combinator, which
 * provides computation over trees.
 * @end[doc]
 *)
declare tree_ind{'z; a, f, g. 'body['a; 'f; 'g]}

(************************************************************************
 * REWRITING                                                            *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The induction combinator takes a $W$-node
 * as its first argument, and a body that expects three arguments $a_2$,
 * $f_2$, and $g_2$.  The $a_2$ argument is the label of the current node,
 * the $f_2$ argument is the function that computes the children, and
 * $g_2$ is the value that is returned by a recursive call.
 * @end[doc]
 *)
prim_rw reduce_tree_ind :
   tree_ind{tree{'a1; 'f1}; a2, f2, g2. 'body['a2; 'f2; 'g2]}
   <--> 'body['a1; 'f1; lambda{a. tree_ind{.'f1 'a; a2, f2, g2. 'body['a2; 'f2; 'g2]}}]

(*! @docoff *)

let resource reduce +=
   (<< tree_ind{tree{'a1; 'f1}; a2, f2, g2. 'body['a2; 'f2; 'g2]} >>, reduce_tree_ind)

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_w
prec prec_tree_ind

dform w_df : except_mode[src] :: parens :: "prec"[prec_w] :: w{'A; x. 'B} =
   mathbbW slot{'x} `":" slot{'A} `"." slot{'B}

dform tree_df : except_mode[src] :: tree{'a; 'f} =
   `"tree(" slot{'a} `"," " " slot{'f} `")"

dform tree_ind_df : except_mode[src] :: parens :: "prec"[prec_tree_ind] :: tree_ind{'z; a, f, g. 'body} =
   szone pushm[3] `"tree_ind(" slot{'g} `"." " "
   pushm[3] `"let tree(" slot{'a} `", " slot{'f} `") =" space slot{'z} space `"in" popm space
   slot{'body} popm ezone

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext W(x:A; B[x])
 * by wFormation A x
 * H >- A = A in Ui
 * H, x:A >- Ui ext B
 *)
prim wFormation 'H 'A 'x :
   sequent [squash] { 'H >- 'A = 'A in univ[i:l] } -->
   ('B['x] : sequent ['ext] { 'H; x: 'A >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] } =
   w{'A; x. 'B['x]}

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Typehood and equality}
 *
 * The $W$-type $@w{x; A; B[x]}$ is well-formed if $A$ is a type,
 * and $B[a]$ is a type for any $a @in A$.
 * @end[doc]
 *)
prim wEquality {| intro []; eqcd |} 'H 'y :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H; y: 'A1 >- 'B1['y] = 'B2['y] in univ[i:l] } -->
   sequent ['ext] { 'H >- w{'A1; x1. 'B1['x1]} = w{'A2; x2. 'B2['x2]} in univ[i:l] } =
   it

(*
 * Typehood.
 *)
prim wType {| intro [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'A1} } -->
   [wf] sequent [squash] { 'H; x: 'A1 >- "type"{'A2['x]} } -->
   sequent ['ext] { 'H >- "type"{.w{'A1; y.'A2['y]}} } =
   it

(*!
 * @docoff
 *)
prim treeFormation {| intro [] |} 'H 'a 'y :
   [wf] sequent [squash] { 'H >- 'a = 'a in 'A } -->
   [main] ('f : sequent ['ext] { 'H >- 'B['a] -> w{'A; x. 'B['x]} }) -->
   [wf] sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- w{'A; x. 'B['x]} } =
   tree{'a; 'f}

(*!
 * @begin[doc]
 * @modsubsection{Membership}
 *
 * The elements of the $W$-type $@w{x; A; B[x]}$ are the
 * @hrefterm[tree] terms $@tree{a; f}$, where $a @in A$,
 * and $f @in B[a] @rightarrow @w{x; A; B[x]}$.
 * @end[doc]
 *)
prim treeEquality {| intro []; eqcd |} 'H 'y :
   [wf] sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   [wf] sequent [squash] { 'H >- 'b1 = 'b2 in 'B['a1] -> w{'A; x. 'B['x]} } -->
   [wf] sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- tree{'a1; 'b1} = tree{'a2; 'b2} in w{'A; x. 'B['x]} } =
   it

(*!
 * @begin[doc]
 * @modsubsection{Elimination}
 *
 * The elimination rule performs induction over the $W$-type
 * $@w{x; A; B[x]}$.  The conclusion is true for all $z$ in the
 * $W$-type if it is true for an arbitrary term $@tree{a; f}$, where
 * the induction hypothesis holds on all children given by $f$.
 * @end[doc]
 *)
prim wElimination {| elim [ThinOption thinT] |} 'H 'J 'z 'a 'f 'g 'b :
   [main] ('t['z; 'a; 'f; 'g] :
   sequent ['ext] { 'H;
                    z: w{'A; x. 'B['x]};
                    'J['z];
                    a: 'A;
                    f: 'B['a] -> w{'A; x. 'B['x]};
                    g: b: 'B['a] -> 'T['f 'b]
                  >- 'T[tree{'a; 'f}]
                  }) -->
   sequent ['ext] { 'H; z: w{'A; x. 'B['x]}; 'J['z] >- 'T['z] } =
      tree_ind{'z; a, f, g. 't['z; 'a; 'f; 'g]}

(*!
 * @begin[doc]
 * @modsubsection{Combinator equality}
 *
 * The tree-induction term computes a value of type $T$ if the body
 * computes a value of type $T$ given and argument $a @in A$, a child
 * function $f$, and a function $g$ that computes the recursive values
 * for each of the children.
 * @end[doc]
 *)
interactive tree_indEquality {| intro []; eqcd |} 'H (w{'A; x. 'B['x]}) bind{z.'T['z]} :
   [wf] sequent [squash] { 'H >- 'z1 = 'z2 in w{'A; x. 'B['x]} } -->
   [wf] sequent [squash] { 'H;
                           a: 'A;
                           f: 'B['a] -> w{'A; x. 'B['x]};
                           g: b: 'B['a] -> 'T['f 'b]
                         >- 'body1['a; 'f; 'g] = 'body2['a; 'f; 'g] in 'T[tree{'a;'f}] } -->
   sequent ['ext] { 'H >- tree_ind{'z1; a, f, g. 'body1['a; 'f; 'g]}
                          = tree_ind{'z2; a2, f2, g2. 'body2['a2; 'f2; 'g2]}
                          in 'T['z1] }

(*! @docoff *)

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let w_term = << w{'A; x. 'B['x]} >>
let w_opname = opname_of_term w_term
let is_w_term = is_dep0_dep1_term w_opname
let dest_w = dest_dep0_dep1_term w_opname
let mk_w_term = mk_dep0_dep1_term w_opname

let tree_term = << tree{'a; 'b} >>
let tree_opname = opname_of_term tree_term
let is_tree_term = is_dep0_dep0_term tree_opname
let dest_tree = dest_dep0_dep0_term tree_opname
let mk_tree_term = mk_dep0_dep0_term tree_opname

let tree_ind_term = << tree_ind{'e; u, v, w. 'b['u; 'v; 'w]} >>
let tree_ind_opname = opname_of_term tree_ind_term
let is_tree_ind_term = is_dep0_dep3_term tree_ind_opname
let dest_tree_ind = dest_dep0_dep3_term tree_ind_opname
let mk_tree_ind_term = mk_dep0_dep3_term tree_ind_opname

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of w
 *)
let resource typeinf += (w_term, infer_univ_dep0_dep1 dest_w)

(*
 * Type of pair.
 * This will be pretty difficult.
 *)
let inf_tree inf consts decls eqs opt_eqs defs t =
   let a, b = dest_tree t in
   let eqs', opt_eqs', defs', a' = inf consts decls eqs opt_eqs defs a in
   let eqs'', opt_eqs'', defs'', b' = inf consts decls eqs' opt_eqs' defs' b in
   let v = Typeinf.vnewname consts defs'' "v" in
      eqs'', opt_eqs'', defs'', mk_w_term v a' b'

let resource typeinf += (tree_term, inf_tree)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
