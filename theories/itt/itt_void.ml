(*!
 * @begin[doc]
 * @theory[Itt_void]
 *
 * The @tt{Itt_void} module defines the @emph{empty} type.
 * The $@void$ type is a subtype of every other type (since
 * it has no elements).
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 *
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
 * @email{jyh@cs.caltech.edu}
 *
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Itt_equal
include Itt_squash
include Itt_subtype
(*! @docoff *)

open Printf
open Mp_debug
open Tactic_type.Sequent
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type.Tacticals

open Base_auto_tactic

open Itt_equal
open Itt_subtype
open Itt_squash

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_void%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*! @terms *)
declare void
(*! @docoff *)

declare top (* we declare it here because we need it for type inference *)

let void_term = << void >>
let void_opname = opname_of_term void_term
let is_void_term = is_no_subterms_term void_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform void_df1 : except_mode[src] :: void = `"Void"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 *
 * @thysubsection{Equality and typehood}
 *
 * The $@void$ type is a member of very universe, and it
 * is a type.
 * @end[doc]
 *
 *)
prim voidEquality {| intro_resource []; eqcd_resource |} 'H :
   sequent ['ext] { 'H >- void IN univ[i:l] } =
   it

(*
 * H >- Ui ext Void
 * by voidFormation
 *)
interactive voidFormation 'H :
   sequent ['ext] { 'H >- univ[i:l] }

(*
 * Typehood.
 *)
prim voidType {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- "type"{void} } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Elimination}
 *
 * Since the $@void$ type is empty, induction over the
 * $@void$ type produces no cases.
 * @end[doc]
 *)
prim voidElimination {| elim_resource [] |} 'H 'J :
   sequent ['ext] { 'H; x: void; 'J['x] >- 'C['x] } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Squash}
 *
 * Any proof of void can be squashed because the proof will never be used.
 * This rule is added to the @hreftactic[squashT] resource.
 * @end[doc]
 *)
interactive void_squashElimination 'H :
   sequent [squash] { 'H >- void } -->
   sequent ['ext] { 'H >- void }

(*!
 * @begin[doc]
 * @thysubsection{Subtyping}
 *
 * The $@void$ type is a subtype of every other type.
 * This rule is derived from the definition of subtyping, and the
 * @hrefrule[voidElimination] rule.
 * @end[doc]
 *)
interactive void_subtype 'H :
   sequent ['ext] { 'H >- subtype{void; 'T} }
(*! @docoff *)

(************************************************************************
 * SQUASH STABILITY                                                     *
 ************************************************************************)

let squash_voidT p =
   void_squashElimination (hyp_count_addr p) p

let squash_resource = Mp_resource.improve squash_resource (void_term, squash_voidT)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

let void_sub p =
   void_subtype (hyp_count_addr p) p

let sub_resource =
   Mp_resource.improve
   sub_resource
   (RLSubtype ([void_term, << 'a >>], void_sub))

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let typeinf_resource = Mp_resource.improve typeinf_resource (void_term, infer_univ1)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
