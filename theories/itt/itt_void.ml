(*
 * Here are rules for the Void base type.
 * Void has no elements.  Its propositional
 * interpretation is "False".
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
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
 * jyh@cs.cornell.edu
 *
 *)

include Tacticals
include Itt_equal
include Itt_subtype

open Printf
open Nl_debug
open Sequent
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Nl_resource

open Tacticals

open Base_auto_tactic

open Itt_equal
open Itt_subtype

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_void%t" eflush

(*
 * incr_debug_level DebugMessage
 * debug_string DebugLoad "Loading itt_void..."
 *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare void

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform void_df1 : mode[prl] :: void = `"Void"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Void
 * by voidFormation
 *)
prim voidFormation 'H : : sequent ['ext] { 'H >- univ[@i:l] } = void

(*
 * H >- Void = Void in Ui ext Ax
 * by voidEquality
 *)
prim voidEquality 'H : : sequent ['ext] { 'H >- void = void in univ[@i:l] } = it

(*
 * Typehood.
 *)
prim voidType 'H : : sequent ['ext] { 'H >- "type"{void} } = it

(*
 * H, i:x:Void, J >- C
 * by voidElimination i
 *)
prim voidElimination 'H 'J : : sequent ['ext] { 'H; x: void; 'J['x] >- 'C['x] } = it

(*
 * Squash stability.
 *)
prim void_squashElimination 'H : sequent [squash] { 'H >- void } :
   sequent ['ext] { 'H >- void } = it

(*
 * Subtyping.
 *)
prim void_subtype 'H : :
   sequent ['ext] { 'H >- subtype{void; 'T} } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Standard term.
 *)
let void_term = << void >>
let void_opname = opname_of_term void_term
let is_void_term = is_no_subterms_term void_opname

(*
 * D
 *)
let d_voidT i p =
   if i = 0 then
      raise (RefineError ("d_voidT", StringError "can't prove void"))
   else
      let t = goal p in
      let i, j = hyp_indices p i in
         voidElimination i j p

let d_resource = d_resource.resource_improve d_resource (void_term, d_voidT)
let dT = d_resource.resource_extract d_resource

let d_void_typeT i p =
   if i = 0 then
      voidType (hyp_count_addr p) p
   else
      raise (RefineError ("d_void_typeT", StringError "no elimination form"))

let void_type_term = << "type"{void} >>

let d_resource = d_resource.resource_improve d_resource (void_type_term, d_void_typeT)

(*
 * EqCD.
 *)
let eqcd_voidT p =
   voidEquality (hyp_count_addr p) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (void_term, eqcd_voidT)
let eqcdT = eqcd_resource.resource_extract eqcd_resource

let equal_void_term = << void = void in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (equal_void_term, d_wrap_eqcd eqcd_voidT)

(************************************************************************
 * SQUASH STABILITY                                                     *
 ************************************************************************)

(*
 * Void is squash stable.
 *)
let squash_void p =
   void_squashElimination (hyp_count_addr p) p

let squash_resource = squash_resource.resource_improve squash_resource (void_term, squash_void)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

let void_sub p =
   void_subtype (hyp_count_addr p) p

let sub_resource =
   sub_resource.resource_improve
   sub_resource
   (RLSubtype ([void_term, << 'a >>], void_sub))

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of void.
 *)
let inf_void _ decl _ = decl, univ1_term

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (void_term, inf_void)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
