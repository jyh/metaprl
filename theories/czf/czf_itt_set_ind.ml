(*
 * Primitiva interactiveatization of implication.
 *
 * ----------------------------------------------------------------
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
 * jyh@cs.cornell.edu
 *)

extends Czf_itt_sep

open Printf
open Mp_debug

open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Var

open Base_dtactic

open Itt_equal
open Itt_struct
open Itt_rfun
open Itt_dprod

open Czf_itt_set
open Czf_itt_eq

let _ =
   show_loading "Loading Czf_itt_set_ind%t"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Dependent function types.
 *)
interactive set_ind_dfun_type (bind{u. 'B['u]}) :
   sequent [squash] { <H> >- isset{'s} } -->
   sequent [squash] { <H>; u: set >- "type"{'B['u]} } -->
   sequent [squash] { <H> >- fun_prop{u. 'B['u]} } -->
   sequent ['ext] { <H> >- "type"{set_ind{'s; T, f, g. x: 'T -> 'B['f 'x]}} }

interactive set_ind_dfun_fun (bind{x. bind{y. 'B['x; 'y]}}) :
   sequent ['ext] { <H> >- fun_set{z. 'A['z]} } -->
   sequent [squash] { <H>; u: set; v: set >- "type"{'B['u; 'v]} } -->
   sequent ['ext] { <H>; u: set >- fun_prop{z. 'B['u; 'z]} } -->
   sequent ['ext] { <H>; v: set >- fun_prop{z. 'B['z; 'v]} } -->
   sequent ['ext] { <H> >- fun_prop{z. set_ind{'A['z]; T, f, g. x: 'T -> 'B['z; 'f 'x]}} }

(*
 * Dependent product types.
 *)
interactive set_ind_dprod_type (bind{u. 'B['u]}) :
   sequent [squash] { <H> >- isset{'s} } -->
   sequent [squash] { <H>; u: set >- "type"{'B['u]} } -->
   sequent [squash] { <H> >- fun_prop{u. 'B['u]} } -->
   sequent ['ext] { <H> >- "type"{set_ind{'s; T, f, g. x: 'T * 'B['f 'x]}} }

interactive set_ind_dprod_fun (bind{x. bind{y. 'B['x; 'y]}}) :
   sequent ['ext] { <H> >- fun_set{z. 'A['z]} } -->
   sequent [squash] { <H>; u: set; v: set >- "type"{'B['u; 'v]} } -->
   sequent ['ext] { <H>; u: set >- fun_prop{z. 'B['u; 'z]} } -->
   sequent ['ext] { <H>; v: set >- fun_prop{z. 'B['z; 'v]} } -->
   sequent ['ext] { <H> >- fun_prop{z. set_ind{'A['z]; T, f, g. x: 'T * 'B['z; 'f 'x]}} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Typehood.
 *)
let d_set_ind_dfun_typeT = funT (fun p ->
   let goal = Sequent.concl p in
   let set_ind = dest_type_term goal in
   let _, f, _, _, b = dest_set_ind set_ind in
   let v, _, b = dest_dfun b in
   let apply = mk_apply_term (mk_var_term f) (mk_var_term v) in
   let goal' = var_subst_to_bind b apply in
      set_ind_dfun_type goal')

let set_ind_dfun_type_term = << "type"{set_ind{'s; T, f, g. x: 'T -> 'B['f; 'x]}} >>

(*
 * Functionality.
 *)
let d_set_ind_dfun_funT = funT (fun p ->
   let goal = Sequent.concl p in
   let x, set_ind = dest_fun_prop goal in
   let _, f, _, _, b = dest_set_ind set_ind in
   let v, _, b = dest_dfun b in
   let apply = mk_apply_term (mk_var_term f) (mk_var_term v) in
   let goal' = mk_xbind_term x (var_subst_to_bind b apply) in
      set_ind_dfun_fun goal')

let set_ind_dfun_fun_term = << fun_prop{z. set_ind{'A['z]; T, f, g. x: 'T -> 'B['z; 'T; 'f; 'g; 'x]}} >>

(*
 * Typehood.
 *)
let d_set_ind_dprod_typeT = funT (fun p ->
   let goal = Sequent.concl p in
   let set_ind = dest_type_term goal in
   let _, f, _, _, b = dest_set_ind set_ind in
   let v, _, b = dest_dprod b in
   let apply = mk_apply_term (mk_var_term f) (mk_var_term v) in
   let goal' = var_subst_to_bind b apply in
      set_ind_dprod_type goal')

let set_ind_dprod_type_term = << "type"{set_ind{'s; T, f, g. x: 'T * 'B['f; 'x]}} >>

(*
 * Functionality.
 *)
let d_set_ind_dprod_funT = funT (fun p ->
   let goal = Sequent.concl p in
   let x, set_ind = dest_fun_prop goal in
   let _, f, _, _, b = dest_set_ind set_ind in
   let v, _, b = dest_dprod b in
   let apply = mk_apply_term (mk_var_term f) (mk_var_term v) in
   let goal' = mk_xbind_term x (var_subst_to_bind b apply) in
      set_ind_dprod_fun goal')

let set_ind_dprod_fun_term = << fun_prop{z. set_ind{'A['z]; T, f, g. x: 'T * 'B['z; 'T; 'f; 'g; 'x]}} >>

let resource intro += [
   set_ind_dfun_type_term, wrap_intro d_set_ind_dfun_typeT;
   set_ind_dfun_fun_term, wrap_intro d_set_ind_dfun_funT;
   set_ind_dprod_type_term, wrap_intro d_set_ind_dprod_typeT;
   set_ind_dprod_fun_term, wrap_intro d_set_ind_dprod_funT
]

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
