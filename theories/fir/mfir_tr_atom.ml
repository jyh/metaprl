(*!
 * @begin[doc]
 * @module[Mfir_tr_atom]
 *
 * The @tt[Mfir_tr_atom] module defines the typing rules for atoms.
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

(*!
 * @docoff
 *)

open Base_dtactic

(**************************************************************************
 * Rules.
 **************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Normal atoms}
 *
 * A variable is well-typed if it is declared to have that type.
 * @end[doc]
 *)

prim ty_atomVar {| elim [] |} 'H 'J :
   sequent [mfir] { 'H; v: var_def{ 'ty; no_def }; 'J['v] >-
      has_type{ atomVar{'v}; 'ty } }
   = it

(*!
 * @begin[doc]
 *
 * An enumeration atom belongs to an enumeration type if its value
 * is in the appropriate range.
 * @end[doc]
 *)

prim ty_atomEnum {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ tyEnum[i:n]; large_type } } -->
   sequent [mfir] { 'H >-
      "and"{ int_le{ 0; 'num }; int_lt{ 'num; number[i:n] } } } -->
   sequent [mfir] { 'H >- has_type{ atomEnum[i:n]{ 'num }; tyEnum[i:n] } }
   = it

(*!
 * @begin[doc]
 *
 * Integer atoms are well-formed if the constant is in the set of 31-bit,
 * signed integers.
 * @end[doc]
 *)

prim ty_atomInt {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ tyInt; large_type } } -->
   sequent [mfir] { 'H >- member{ 'i; intset_max } } -->
   sequent [mfir] { 'H >- has_type{ atomInt{'i}; tyInt } }
   = it

(*!
 * @begin[doc]
 * @modsubsection{Unary and binary operators}
 *
 * For the terms $<< atomUnop{ 'unop; 'a } >>$ and
 * $<< atomBinop{ 'binop; 'a1; 'a2 } >>$, there is a typing rule for each
 * possible operator.  The rules are straightforward, and we will illustrate
 * their basic form with two examples.
 * @end[doc]
 *)

prim ty_uminusIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type{ 'atom ; tyInt } } -->
   sequent [mfir] { 'H >- has_type{ atomUnop{ uminusIntOp; 'atom }; tyInt } }
   = it

prim ty_plusIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >- has_type{ atomBinop{plusIntOp; 'a1; 'a2}; tyInt } }
   = it

(*!
 * @docoff
 *)

(* TODO: write up the remaining unop/binop rules. *)
