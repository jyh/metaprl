(*!
 * @spelling{memberFormation srec srecind unrollings}
 *
 * @begin[doc]
 * @theory[Itt_srec]
 *
 * The @tt{Itt_srec} module defines a ``simple'' recursive type,
 * without parameters that are passed along the unrollings of the
 * type, as it is in the parameterized recursive type in @hreftheory[Itt_prec].
 *
 * The syntax of the recursive type is $@srec{T; B[T]}$.  The variable
 * $T$ represents the type itself, which is given through the
 * interpretation $T = B[T]$.  The body $B[T]$ must be a type for
 * @emph{any} type $T @in @univ{i}$, and in addition $B[T]$ must be
 * monotone in the type argument $T$.
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
include Itt_prec
include Itt_subtype
include Itt_void
include Itt_struct
(*! @docoff *)

open Printf
open Mp_debug
open String_set
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type.Tacticals
open Var

open Base_dtactic

open Itt_void
open Itt_equal
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_srec%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The @tt{srec} term defines the recursive type.  The @tt{srecind}
 * term defines an induction combinator over elements of the recursive type.
 * @end[doc]
 *)
declare srec{T. 'B['T]}
declare srecind{'a; p, h. 'g['p; 'h]}
(*! @docoff *)

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform srec_df : except_mode[src] :: srec{T. 'B} =
   szone mu `"{" slot{'T} `"." pushm[0] slot{'B} `"}" popm ezone

dform srecind_df : except_mode[src] :: srecind{'a; p, h. 'g} =
   szone pushm[3]
   `"srecind(" slot{'a} `";" hspace
   slot{'p} `"," slot{'p} `"." hspace
   slot{'g}
   popm ezone

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The @tt{srecind} induction combinator takes an argument
 * $a$ that belongs to a recursive type definition.  The computation
 * is defined through the body $g[p, h]$, which takes a
 * recursive instance $p$, and the argument element $h$.
 * @end[doc]
 *)
prim_rw unfold_srecind : srecind{'a; p, h. 'g['p; 'h]} <-->
   'g[lambda{a. srecind{'a; p, h. 'g['p; 'h]}}; 'a]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @docoff
 *)
prim srecFormation 'H 'T :
   ('B['T] : sequent ['ext] { 'H; T: univ[i:l] >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] } =
   srec{T. 'B['T]}

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Typehood and equality}
 *
 * The simple recursive type $@srec{T; B[T]}$ is a type if $B[T]$ is
 * a monotone type over types type $T @in @univ{i}$.
 * @end[doc]
 *)
prim srecEquality {| intro []; eqcd |} 'H 'T 'S1 'S2 'z :
   [wf] sequent [squash] { 'H; T: univ[i:l] >- 'B1['T] = 'B2['T] in univ[i:l] } -->
   [wf] sequent [squash] { 'H; S1: univ[i:l]; S2: univ[i:l]; z: subtype{'S1; 'S2} >- subtype{'B1['S1]; 'B1['S2]} } -->
   sequent ['ext] { 'H >- srec{T1. 'B1['T1]} = srec{T2. 'B2['T2]} in univ[i:l] } =
   it

prim srecType {| intro [] |} 'H 'S1 'S2 'z univ[i:l] :
   [wf] sequent [squash] { 'H; S1: univ[i:l]; S2: univ[i:l]; z: subtype{'S1; 'S2} >- subtype{'B['S1]; 'B['S2]} } -->
   sequent ['ext] { 'H >- "type"{srec{T. 'B['T]}} } =
   it

(*!
 * @docoff
 *)
prim srec_memberFormation {| intro [] |} 'H :
   [wf] ('g : sequent ['ext] { 'H >- 'B[srec{T. 'B['T]}] }) -->
   [wf] sequent [squash] { 'H >- "type"{(srec{T. 'B['T]})} } -->
   sequent ['ext] { 'H >- srec{T. 'B['T]} } =
   'g

(*!
 * @begin[doc]
 * @thysubsection{Membership}
 *
 * The elements of the recursive type $@srec{T; B[T]}$ are the
 * elements of $B[@srec{T; B[T]}]$.
 * @end[doc]
 *)
prim srec_memberEquality {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'x1 = 'x2 in 'B[srec{T. 'B['T]}] } -->
   [wf] sequent [squash] { 'H >- "type"{(srec{T. 'B['T]})} } -->
   sequent ['ext] { 'H >- 'x1 = 'x2 in srec{T. 'B['T]} } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Elimination}
 *
 * The elimination form performs induction over the
 * assumption $x@colon @srec{T; B[T]}$.  The conclusion $C[x]$ is
 * true for the arbitrary element $x$, if, given that it holds on
 * the unrollings, it also holds on $x$.
 * @end[doc]
 *)
prim srecElimination {| elim [ThinOption thinT] |} 'H 'J 'x srec{T. 'B['T]} 'T1 'u 'v 'w 'z univ[i:l] :
   [main] ('g['x; 'T1; 'u; 'w; 'z] : sequent ['ext] {
             'H;
             x: srec{T. 'B['T]};
             'J['x];
             T1: univ[i:l];
             u: subtype{'T1; srec{T. 'B['T]}};
             w: v: 'T1 -> 'C['v];
             z: 'B['T1]
           >- 'C['z]
           }) -->
   sequent ['ext] { 'H; x: srec{T. 'B['T]}; 'J['x] >- 'C['x] } =
   srecind{'x; p, h. 'g['x; srec{T. 'B['T]}; it; 'p; 'h]}

(*!
 * @begin[doc]
 * The second elimination form performs unrolling of the recursive
 * type definition.
 * @end[doc]
 *)
prim srecUnrollElimination {| elim [ThinOption thinT] |} 'H 'J 'x 'y 'u :
   [main] ('g['x; 'y; 'u] : sequent ['ext] { 'H; x: srec{T. 'B['T]}; 'J['x]; y: 'B[srec{T. 'B['T]}]; u: 'x = 'y in 'B[srec{T. 'B['T]}] >- 'C['y] }) -->
   sequent ['ext] { 'H; x: srec{T. 'B['T]}; 'J['x] >- 'C['x] } =
   'g['x; 'x; it]

(*!
 * @begin[doc]
 * @thysubsection{Combinator equality}
 *
 * The @hrefterm[srecind] term produces a value of type $S$ if the
 * argument belongs to some recursive type, and the body computes
 * a value of type $S$ given the argument $r$ and a function
 * $h$ to compute the values of the recursive calls.
 * @end[doc]
 *)
prim srecindEquality {| intro []; eqcd |} 'H lambda{x. 'S['x]} srec{T. 'B['T]} 'T1 'u 'v 'w 'z univ[i:l] :
   [wf] sequent [squash] { 'H >- 'r1 = 'r2 in srec{T. 'B['T]} } -->
   [wf] sequent [squash] { 'H; T1: univ[i:l]; z: subtype{'T1; srec{T. 'B['T]}};
               v: w: 'T1 -> 'S['w]; w: 'B['T1]
           >- 't1['v; 'w] = 't2['v; 'w] in 'S['w]
           } -->
   sequent ['ext] { 'H >- srecind{'r1; h1, z1. 't1['h1; 'z1]}
                   = srecind{'r2; h2, z2. 't2['h2; 'z2]}
                   in 'S['r1]
           } =
   it
(*! @docoff *)

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let srec_term = << srec{T. 'B['T]} >>
let srec_opname = opname_of_term srec_term
let is_srec_term = is_dep1_term srec_opname
let dest_srec = dest_dep1_term srec_opname
let mk_srec_term = mk_dep1_term srec_opname

let srecind_term = << srecind{'a; p, h. 'g['p; 'h]} >>
let srecind_opname = opname_of_term srecind_term
let is_srecind_term = is_dep0_dep2_term srecind_opname
let dest_srecind = dest_dep0_dep2_term srecind_opname
let mk_srecind_term = mk_dep0_dep2_term srecind_opname

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of srec.
 *)
let inf_srec inf consts decls eqs opt_eqs defs t =
   let a, body = dest_srec t in
      inf (StringSet.add a consts) ((a,univ1_term)::decls) eqs opt_eqs defs body

let resource typeinf += (srec_term, inf_srec)

(*
 * Type of srecind.
 * WRONG according to jyh.
let inf_srecind f decl t =
   let p, h, a, g = dest_srecind t in
   let decl', a' = f decl a in
      f (eqnlist_append_var_eqn p a' (eqnlist_append_var_eqn h a' decl')) g

let resource typeinf += (srecind_term, inf_srecind)
*)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
