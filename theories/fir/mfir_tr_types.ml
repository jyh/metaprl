(*!
 * @begin[doc]
 * @module[Mfir_tr_types]
 *
 * The @tt[Mfir_tr_types] module defines type equality judgments, which are
 * used to define type well-formedness.
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
 *
 * Two type variables are equal if they name the same variable, and the
 * variable is declared in the context with the specified kind.
 * @end[doc]
 *)

prim wf_tyVar {| elim [] |} 'H 'J :
   sequent [mfir] { 'H; tv: ty_def{ 'k; no_def}; 'J['tv] >-
      type_eq{ tyVar{ 'tv }; tyVar{ 'tv }; 'k } }
   = it

(*!
 * @begin[doc]
 *
 * An enumeration type is well-formed if the parameter is within the allowed
 * range of values.
 * @end[doc]
 *)

prim wf_tyEnum {| intro [] |} 'H :
   sequent [mfir] { 'H >- member{ number[i:n]; enum_max } } -->
   sequent [mfir] { 'H >- type_eq{ tyEnum[i:n]; tyEnum[i:n]; small_type } }
   = it

(*!
 * @begin[doc]
 *
 * The equality judgments for numeric data types are straightforward. Note
 * that $<< tyRawInt[precision:n, "signed"] >>$,
 * $<< tyRawInt[precision:n, "unsigned"] >>$,
 * and $<< tyFloat[precision:n] >>$
 * cannot be used as $<< small_type >>$ types.
 * @end[doc]
 *)

prim wf_tyInt {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ tyInt; tyInt; small_type } }
   = it

prim wf_tyRawInt_signed {| intro [] |} 'H :
   sequent [mfir] { 'H >-
      "or"{ int_eq{ number[precision:n]; 8 };
      "or"{ int_eq{ number[precision:n]; 16 };
      "or"{ int_eq{ number[precision:n]; 32 };
            int_eq{ number[precision:n]; 64 } } } } } -->
   sequent [mfir] { 'H >- type_eq{ tyRawInt[precision:n, "signed"];
                                   tyRawInt[precision:n, "signed"];
                                   large_type } }
   = it

prim wf_tyRawInt_unsigned {| intro [] |} 'H :
   sequent [mfir] { 'H >-
      "or"{ int_eq{ number[precision:n]; 8 };
      "or"{ int_eq{ number[precision:n]; 16 };
      "or"{ int_eq{ number[precision:n]; 32 };
            int_eq{ number[precision:n]; 64 } } } } } -->
   sequent [mfir] { 'H >- type_eq{ tyRawInt[precision:n, "unsigned"];
                                   tyRawInt[precision:n, "unsigned"];
                                   large_type } }
   = it

prim wf_tyFloat {| intro [] |} 'H :
   sequent [mfir] { 'H >-
      "or"{ int_eq{ number[precision:n]; 32 };
      "or"{ int_eq{ number[precision:n]; 64 };
            int_eq{ number[precision:n]; 80 } } } } -->
   sequent [mfir] { 'H >- type_eq{ tyFloat[precision:n];
                                   tyFloat[precision:n];
                                   large_type } }
   = it

(*!
 * @begin[doc]
 *
 * Two tuple types are equal if they have the same ``class'', and they are
 * pointwise equal.  Note that ``box'' tuples must have arity one.
 * @end[doc]
 *)

prim wf_tyTuple_box {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ 't1; 't2; large_type } } -->
   sequent [mfir] { 'H >- type_eq{ tyTuple["box"]{ cons{ 't1; nil } };
                                   tyTuple["box"]{ cons{ 't2; nil } };
                                   small_type } }
   = it

prim wf_tyTuple_normal1 {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ 'h1; 'h2; large_type } } -->
   sequent [mfir] { 'H >- type_eq{ tyTuple["normal"]{ 't1 };
                                   tyTuple["normal"]{ 't2 };
                                   small_type } } -->
   sequent [mfir] { 'H >- type_eq{ tyTuple["normal"]{ cons{ 'h1; 't1 } };
                                   tyTuple["normal"]{ cons{ 'h2; 't2 } };
                                   small_type } }
   = it

prim wf_tyTuple_normal2 {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ tyTuple["normal"]{ nil };
                                   tyTuple["normal"]{ nil };
                                   small_type } }
   = it

(*!
 * @begin[doc]
 *
 * Two array types are equal if their element types are equal.
 * @end[doc]
 *)

prim wf_tyArray {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ 't1; 't2; large_type } } -->
   sequent [mfir] { 'H >- type_eq{ tyArray{'t1}; tyArray{'t2}; small_type } }
   = it

(*!
 * @begin[doc]
 *
 * Rawdata is an opaque data space used to represent data without strict
 * typing rules, such as heap data in C.
 * @end[doc]
 *)

prim wf_tyRawData {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ tyRawData; tyRawData; small_type } }
   = it

(*!
 * @begin[doc]
 *
 * Two function types are equal if their arguments types are equal, and if
 * the types of their return values are equal.
 * @end[doc]
 *)

prim wf_tyFun {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ 'a1; 'a2; large_type } } -->
   sequent [mfir] { 'H >- type_eq{ 'r1; 'r2; large_type } } -->
   sequent [mfir] { 'H >- type_eq{ tyFun{ 'a1; 'r1 };
                                   tyFun{ 'a2; 'r2 };
                                   small_type } }
   = it

(*!
 * @docoff
 *)
