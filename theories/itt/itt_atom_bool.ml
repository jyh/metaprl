(*
 * Theorems about atoms.
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
 *)

include Itt_atom
include Itt_bool

open Mp_resource

open Tacticals

open Itt_equal

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

prec prec_eq_atom

declare eq_atom{'x; 'y}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform eq_atom_df : mode[prl] :: parens :: "prec"[prec_eq_atom] :: eq_atom{'x; 'y} =
   slot{'x} space `"=" suba slot{'y}

(************************************************************************
 * REWRITE                                                              *
 ************************************************************************)

primrw reduce_eq_atom : eq_atom{token[@x:t]; token[@y:t]} <--> bool_flag[@x = @y]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

prim eq_atom_wf 'H :
   sequent [squash] { 'H >- member{atom; 'x} } -->
   sequent [squash] { 'H >- member{atom; 'y} } -->
   sequent ['ext] { 'H >- member{bool; eq_atom{'x; 'y}} } =
   it

prim eq_atom_assert_intro 'H :
   sequent [squash] { 'H >- 'x = 'y in atom } -->
   sequent ['ext] { 'H >- "assert"{eq_atom{'x; 'y}} } =
   it

prim eq_atom_assert_elim 'H 'J :
   sequent ['ext] { 'H; x: 'a = 'b in atom; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{eq_atom{'a; 'b}}; 'J['x] >- 'C['x] } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Well-formedness.
 *)
let d_atom_wfT p =
   (eq_atom_wf (Sequent.hyp_count_addr p)
    thenT addHiddenLabelT "wf") p

let atom_wf_term = << member{bool; eq_atom{'x; 'y}} >>

let d_resource = Mp_resource.improve d_resource (atom_wf_term, wrap_intro d_atom_wfT)

(*
 * Equality.
 *)
let d_eq_atom_assertT i p =
   if i = 0 then
      eq_atom_assert_intro (Sequent.hyp_count_addr p) p
   else
      let j, k = Sequent.hyp_indices p i in
         eq_atom_assert_elim j k p

let eq_atom_assert_term = << "assert"{eq_atom{'v1; 'v2}} >>

let d_resource = Mp_resource.improve d_resource (eq_atom_assert_term, d_eq_atom_assertT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
