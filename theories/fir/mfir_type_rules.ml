(*!
 * @spelling{pointwise}
 *
 * @begin[doc]
 * @module[Mfir_type_rules]
 *
 * The @tt[Mfir_type_rules] module defines the FIR type system.
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

extends Base_theory
extends Mfir_basic
extends Mfir_ty
extends Mfir_exp
extends Mfir_sequent

open Base_dtactic

(**************************************************************************
 * Rules.
 **************************************************************************)

(*!
 * @begin[doc]
 * @modsection{Side conditions}
 *
 * Proofs of side-conditions require a proof of $<< "true" >>$, which we
 * take to be an axiom.
 * @end[doc]
 *)

prim truth_intro {| intro [] |} 'H :
   sequent [mfir] { 'H >- "true" }
   = it

(*!
 * @begin[doc]
 * @modsection{Store typing rules}
 *
 * The typing rules for functions are straightforward.  The body of the
 * function must be typed as the result type of the function, assuming that
 * its binding variable has the appropriate type (or kind).
 * @end[doc]
 *)

prim ty_store_lambda {| intro [] |} 'H 'a :
   sequent [mfir] { 'H; a: var_def{ 'arg_type; no_def } >-
      has_type{ 'f['a]; 'res_type } } -->
   sequent [mfir] { 'H >-
      has_type{ lambda{ v. 'f['v] }; tyFun{ 'arg_type; 'res_type } } }
   = it

prim ty_store_polyFun {| intro [] |} 'H 'a :
   sequent [mfir] { 'H; a: ty_def{ small_type; no_def } >-
      has_type{ 'f['a]; 'ty['a] } } -->
   sequent [mfir] { 'H >-
      has_type{ polyFun{ t. 'f['t] }; tyAll{ t. 'ty['t] } } }
   = it

(*!
 * @begin[doc]
 * @modsection{Type equality}
 *
 * Type well-formedness judgments are expressed as a set of type
 * equality judgments.  The @tt[wf_small_type] rule allows any
 * $<< small_type >>$ type to be used as a $<< large_type >>$.
 * @end[doc]
 *)

prim wf_small_type {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ 'ty1; 'ty2; small_type } } -->
   sequent [mfir] { 'H >- type_eq{ 'ty1; 'ty2; large_type } }
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
 * that $<< tyRawInt[precision:n, sign:s] >>$ and $<< tyFloat[precision:n] >>$
 * cannot be used as $<< small_type >>$ types.
 * @end[doc]
 *)

prim wf_tyInt {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ tyInt; tyInt; small_type } }
   = it

prim wf_tyRawInt {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ tyRawInt[precision:n, sign:s];
                                   tyRawInt[precisoin:n, sign:s];
                                   large_type } }
   = it

prim wf_tyFloat {| intro [] |} 'H :
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
   sequent [mfir] { 'H >- type_eq{ 'ty1; 'ty2; large_type } } -->
   sequent [mfir] { 'H >-
      type_eq{ tyTuple["box"]{ cons{ 'ty1; nil } };
               tyTuple["box"]{ cons{ 'ty2; nil } };
               small_type } }
   = it

prim wf_tyTuple_normal1 {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ 'h1; 'h2; large_type } } -->
   sequent [mfir] { 'H >-
      type_eq{ tyTuple["normal"]{ 't1 };
               tyTuple["normal"]{ 't2 };
               small_type } } -->
   sequent [mfir] { 'H >-
      type_eq{ tyTuple["normal"]{ cons{ 'h1; 't1 } };
               tyTuple["normal"]{ cons{ 'h2; 't2 } };
               small_type } }
   = it

prim wf_tyTuple_normal2 {| intro [] |} 'H :
   sequent [mfir] { 'H >-
      type_eq{ tyTuple["normal"]{ nil };
               tyTuple["normal"]{ nil };
               small_type } }
   = it

(*!
 * @begin[doc]
 * @modsection{Atom typing rules}
 *
 * Integer atoms are well-formed if the constant is in the set of 31-bit,
 * signed integers.
 * @end[doc]
 *)

prim ty_atomInt {| intro [] |} 'H :
   sequent [mfir] { 'H >- member{ 'i; intset_max } } -->
   sequent [mfir] { 'H >- has_type{ atomInt{'i}; tyInt } }
   = it

(*!
 * @begin[doc]
 *
 * A variable is well-typed if it is declared to have that type.
 * @end[doc]
 *)

prim ty_atomVar {| elim [] |} 'H 'J 'v :
   sequent [mfir] { 'H; v: var_def{ 'ty; no_def }; 'J['v] >-
      has_type{ atomVar{'v}; 'ty } }
   = it

(*!
 * @docoff
 *)
