(*!
 * @begin[doc]
 * @module[Mfir_tr_exp]
 *
 * The @tt[Mfir_tr_exp] module defines the typing rules for expressions.
 * @end[doc]
 *
 * ------------------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.  Additional
 * information about the system is available at
 * http://www.metaprl.org/
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
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
 * Author: Brian Emre Aydemir
 * @email{emre@cs.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)

extends Base_theory
extends Mfir_basic
extends Mfir_ty
extends Mfir_exp
extends Mfir_sequent
extends Mfir_tr_base
extends Mfir_tr_types
extends Mfir_tr_atom
extends Mfir_tr_store

(*!
 * @docoff
 *)

open Tactic_type
open Tactic_type.Tacticals
open Base_auto_tactic
open Base_dtactic
open Mfir_auto

(**************************************************************************
 * Rules.
 **************************************************************************)

(*!
 * @begin[doc]
 * @rules
 *
 * Operationally, the $<< letAtom{ 'ty1; 'atom; v. 'exp['v] } >>$ expression
 * binds $<< 'atom >>$ to $<< 'v >>$ in $<< 'exp >>$.  The expression has type
 * $<< 'ty2 >>$ if $<< 'atom >>$ has type $<< 'ty1 >>$, and $<< 'exp['v] >>$
 * has type $<< 'ty2 >>$ assuming that $<< 'v >>$ has type $<< 'ty1 >>$.
 * @end[doc]
 *)

prim ty_letAtom {| intro [] |} 'H 'a :
   sequent [mfir] { 'H >- has_type["atom"]{ 'atom; 'ty1 } } -->
   sequent [mfir] { 'H; a: var_def{ 'ty1; no_def } >-
      has_type["exp"]{ 'exp['a]; 'ty2 } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{ letAtom{ 'ty1; 'atom; v. 'exp['v] }; 'ty2 } }
   = it

(* XXX letExt *)

(*!
 * @begin[doc]
 *
 * The next three rules assume that FIR programs are written in continuation
 * passing style.  A function call is well-formed if the variable
 * $<< atomVar{'v} >>$ is a function, and if the arguments have the
 * appropriate types.  Note that the type of $<< atomVar{'v} >>$ must be a
 * function type that ``returns'' a value of type $<< tyEnum[0] >>$. Also note
 * that in the two auxilary rules below (@tt[ty_tailCall_args1] and
 * @tt[ty_tailCall_args2]), the well-formedness of the types is ensured by the
 * sequent used in the application of the @tt[ty_tailCall] rule.
 * @end[doc]
 *)

prim ty_tailCall 'H 'J :
   sequent [mfir] { 'H; v: var_def{ tyFun{'t1; 't2}; no_def }; 'J['v] >-
      has_type["tailCall"]{ 'atom_list; tyFun{ 't1; 't2 } } } -->
   sequent [mfir] { 'H; v: var_def{ tyFun{'t1; 't2}; no_def }; 'J['v] >-
      has_type["exp"]{ tailCall{ atomVar{'v}; 'atom_list }; tyEnum[0] } }
   = it

prim ty_tailCall_args1 {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'h; 't1 } } -->
   sequent [mfir] { 'H >- has_type["tailCall"]{ 't; 't2 } } -->
   sequent [mfir] { 'H >-
      has_type["tailCall"]{ cons{ 'h; 't }; tyFun{ 't1; 't2 } } }
   = it

prim ty_tailCall_args2 {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["tailCall"]{ nil; tyEnum[0] } }
   = it

(*!
 * @docoff
 *)

let d_ty_tailCall i p =
   let j, k = Sequent.hyp_indices p i in
      ty_tailCall j k p

let resource auto += {
   auto_name = "d_ty_tailCall";
   auto_prec = fir_auto_prec;
   auto_tac = onSomeHypT d_ty_tailCall;
   auto_type = AutoNormal
}

(* XXX matchExp *)

(* XXX letAlloc *)

(* XXX Subscript *)

(*!
 * @begin[doc]
 *
 * The expression $<< letGlobal{ 'ty1; 'label; v. 'exp['v] } >>$ is used to
 * read a global value, and the expression
 * $<< setGlobal{ 'label; 'ty1; 'atom; 'exp } >>$ is used to set a global
 * value.  There is no way to use global values directly.  The typing rules
 * for these expressions are straightforward.
 * @end[doc]
 *)

prim ty_label 'H 'J :
   sequent [mfir] { 'H; l: global_def{ 'ty; no_def }; 'J['l] >-
      has_type["label"]{ 'l; 'ty } }
   = it

prim ty_letGlobal {| intro [] |} 'H 'a :
   sequent [mfir] { 'H >- has_type["label"]{ 'label; 'ty1 } } -->
   sequent [mfir] { 'H; a: var_def{ 'ty1; no_def } >-
      has_type["exp"]{ 'exp['a]; 'ty2 } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{ letGlobal{ 'ty1; 'label; v. 'exp['v] }; 'ty2 } }
   = it

prim ty_setGlobal {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["label"]{ 'label; 'ty1 } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'atom; 'ty1 } } -->
   sequent [mfir] { 'H >- has_type["exp"]{ 'exp; 'ty2 } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{ setGlobal{ 'label; 'ty1; 'atom; 'exp }; 'ty2 } }
   = it

(*!
 * @docoff
 *)

let d_ty_label i p =
   let j, k = Sequent.hyp_indices p i in
      ty_label j k p

let resource auto += {
   auto_name = "d_ty_label";
   auto_prec = fir_auto_prec;
   auto_tac = onSomeHypT d_ty_label;
   auto_type = AutoNormal
}
