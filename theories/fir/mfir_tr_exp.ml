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
 * @modsubsection{Basic expressions}
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

(*!
 * @begin[doc]
 *
 * The expression $<< letExt[str:s]{ 'u; 'tyl; 'args; v. 'exp['v] } >>$ binds
 * the result of a call to an @it[external] (e.g.~standard library) function
 * $<< 'str >>$ to $<< 'v >>$ in $<< 'exp >>$.  We make no attempt to see that
 * the types in the expression correspond to the actual types for the function
 * @tt[str].
 * @end[doc]
 *)

prim ty_letExt {| intro [] |} 'H 'a :
   sequent [mfir] { 'H >- has_type["atom_list"]{ 'args; 'tyl } } -->
   sequent [mfir] { 'H; a: var_def{ 'u; no_def } >-
      has_type["exp"]{ 'exp['a]; 't } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{ letExt[str:s]{ 'u; 'tyl; 'args; v. 'exp['v] };
                       't } }
   = it

(*!
 * @begin[doc]
 *
 * The next three rules assume that FIR programs are written in continuation
 * passing style.  A function call is well-formed if the variable
 * $<< atomVar{'v} >>$ is a function, and if the arguments have the
 * appropriate types.  Note that the type of $<< atomVar{'v} >>$ must be a
 * function type that ``returns'' a value of type $<< tyEnum[0] >>$. Note
 * that in the two auxilary rules below (@tt[ty_tailCall_args1] and
 * @tt[ty_tailCall_args2]), the well-formedness of the types is ensured by the
 * sequent used in the application of the @tt[ty_tailCall] rule.
 * @end[doc]
 *)

prim ty_tailCall 'H 'J :
   sequent [mfir] { 'H; v: var_def{ tyFun{'t1; 't2}; no_def }; 'J['v] >-
      has_type["tailCall"]{ 'atoms; tyFun{ 't1; 't2 } } } -->
   sequent [mfir] { 'H; v: var_def{ tyFun{'t1; 't2}; no_def }; 'J['v] >-
      has_type["exp"]{ tailCall{ atomVar{'v}; 'atoms }; tyEnum[0] } }
   = it

prim ty_tailCall_args1 {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["tailCall"]{ nil; tyEnum[0] } }
   = it

prim ty_tailCall_args2 {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'h; 't1 } } -->
   sequent [mfir] { 'H >- has_type["tailCall"]{ 't; 't2 } } -->
   sequent [mfir] { 'H >-
      has_type["tailCall"]{ cons{ 'h; 't }; tyFun{ 't1; 't2 } } }
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

(*!
 * @begin[doc]
 * @modsubsection{Pattern matching}
 *
 * ...
 * @end[doc]
 *)

(* XXX matching *)

(*!
 * @begin[doc]
 * @modsubsection{Allocation}
 *
 * An offset atom should either be an integer or a raw integer.
 * Note that offsets cannot be negative.
 * @end[doc]
 *)

prim ty_offset_tyInt {| intro [] |} 'H :
   sequent [mfir] { 'H >- int_le{ 0; 'i } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ atomInt{'i}; tyInt } } -->
   sequent [mfir] { 'H >- has_type["offset"]{ atomInt{'i}; offset } }
   = it

prim ty_offset_tyRawInt {| intro [] |} 'H :
   sequent [mfir] { 'H >- int_le{ 0; 'i } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ atomRawInt[32, "signed"]{'i};
                                            tyRawInt[32, "signed"] } } -->
   sequent [mfir] { 'H >- has_type["offset"]{ atomRawInt[32, "signed"]{'i};
                                              offset } }
   = it

(*!
 * @begin[doc]
 *
 * The rules for the expression $<< letAlloc{ 'op; v. 'exp['v] } >>$
 * defer, when possible, to the rules for the well-formedness of
 * the value allocated.  The result of the allocation is bound to $<< 'v >>$
 * in $<< 'exp >>$.
 * @end[doc]
 *)

prim ty_letAlloc_tuple {| intro [] |} 'H 'a :
   sequent [mfir] { 'H >- has_type["store"]{'atoms; tyTuple[tc:s]{'tyl}} } -->
   sequent [mfir] { 'H; a: var_def{ tyTuple[tc:s]{'tyl}; no_def } >-
      has_type["exp"]{ 'exp['a]; 't } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{
         letAlloc{allocTuple[tc:s]{tyTuple[tc:s]{'tyl}; 'atoms}; v. 'exp['v]};
         't } }
   = it

prim ty_letAlloc_union {| intro [] |} 'H 'a :
   sequent [mfir] { 'H >-
      has_type["store"]{ union_val[i:n]{ 'tv; 'atoms }; 'ty } } -->
   sequent [mfir] { 'H; a: var_def{ 'ty; no_def } >-
      has_type["exp"]{ 'exp['a]; 't } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{
         letAlloc{ allocUnion[i:n]{ 'ty; 'tv; 'atoms }; v. 'exp['v] };
         't } }
   = it

(*!
 * @begin[doc]
 *
 * For array and raw data allocation, we only validate the size
 * of the area allocated, and in the case of arrays, the initializer value.
 * @end[doc]
 *)

prim ty_letAlloc_varray {| intro [] |} 'H 'a :
   sequent [mfir] { 'H >- has_type["offset"]{ 'a1; offset } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; 'u } } -->
   sequent [mfir] { 'H; a: var_def{ tyArray{'u}; no_def } >-
      has_type["exp"]{ 'exp['a]; 't } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{
         letAlloc{ allocVArray{tyArray{'u}; 'a1; 'a2 }; v. 'exp['v] };
         't } }
   = it

prim ty_letAlloc_malloc {| intro [] |} 'H 'a :
   sequent [mfir] { 'H >- has_type["offset"]{ 'atom; offset } } -->
   sequent [mfir] { 'H; a: var_def{ tyRawData; no_def } >-
      has_type["exp"]{ 'exp['a]; 't } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{
         letAlloc{ allocMalloc{ tyRawData; 'atom }; v. 'exp['v] };
         't } }
   = it

(*!
 * @begin[doc]
 * @modsubsection{Subscripting}
 *
 * ...
 * @end[doc]
 *)

(* XXX subscrripting *)

(*!
 * @begin[doc]
 * @modsubsection{Globals}
 *
 * The expression $<< letGlobal{ 'ty1; 'label; v. 'exp['v] } >>$ is used to
 * read a global value, and the expression
 * $<< setGlobal{ 'label; 'ty1; 'atom; 'exp } >>$ is used to set a global
 * value.  There is no way to use global values directly.  The typing rules
 * for these expressions are straightforward.
 * @end[doc]
 *)

prim ty_label 'H 'J :
   sequent [mfir] { 'H; l: global_def{ 'ty; 'd }; 'J['l] >-
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
