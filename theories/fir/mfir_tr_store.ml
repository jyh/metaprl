(*!
 * @begin[doc]
 * @module[Mfir_tr_store]
 *
 * The @tt[Mfir_tr_store] module defines the typing rules for store values.
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
 *
 * The typing rules for functions are straightforward.  The body of the
 * function must be typed as the result type of the function, assuming that
 * its binding variable has the appropriate type (or kind). Note that
 * for $<< polyFun{ x. 'f['x] } >>$ to be well-formed, $f$ must be a function.
 * @end[doc]
 *)

prim ty_store_lambda {| intro [] |} 'H 'a :
   sequent [mfir] { 'H >-
      type_eq{ tyFun{ 'arg_type; 'res_type }; large_type } } -->
   sequent [mfir] { 'H >- type_eq{ 'arg_type; large_type } } -->
   sequent [mfir] { 'H; a: var_def{ 'arg_type; no_def } >-
      has_type["exp"]{ 'f['a]; 'res_type } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{ lambda{ v. 'f['v] }; tyFun{ 'arg_type; 'res_type } } }
   = it

prim ty_store_polyFun1 {| intro [] |} 'H 'a :
   sequent [mfir] { 'H >- type_eq{ tyAll{ t. 'ty['t] }; large_type } } -->
   sequent [mfir] { 'H; a: ty_def{ small_type; no_def } >-
      has_type["exp"]{ polyFun{ y. 'f['a; 'y] }; 'ty['a] } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{ polyFun{ x. polyFun{ y. 'f['x; 'y] } };
                       tyAll{ t. 'ty['t] } } }
   = it

prim ty_store_polyFun2 {| intro [] |} 'H 'a :
   sequent [mfir] { 'H >- type_eq{ tyAll{ t. 'ty['t] }; large_type } } -->
   sequent [mfir] { 'H; a: ty_def{ small_type; no_def } >-
      has_type["exp"]{ lambda{ y. 'f['a; 'y] }; 'ty['a] } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{ polyFun{ x. lambda{ y. 'f['x; 'y] } };
                       tyAll{ t. 'ty['t] } } }
   = it

(*!
 * @docoff
 *)
