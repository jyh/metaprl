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
 * Store values of a tuple types are represented as lists of atoms.
 * @end[doc]
 *)

prim ty_store_tuple_box {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'elt; 't } } -->
   sequent [mfir] { 'H >-
      has_type["store"]{ cons{ 'elt; nil };
                         tyTuple["box"]{ cons{ 't; nil } } } }
   = it

prim ty_store_tuple_normal {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom_list"]{ 'elts; 'types } } -->
   sequent [mfir] { 'H >- has_type["store"]{'elts; tyTuple["normal"]{'types}} }
   = it

(*!
 * @begin[doc]
 *
 * Store values of array types are also represented as lists of atoms.
 * @end[doc]
 *)

prim ty_store_array1 {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'elt; 't } } -->
   sequent [mfir] { 'H >- has_type["store"]{ 'tail; tyArray{'t} } } -->
   sequent [mfir] { 'H >- has_type["store"]{cons{'elt; 'tail}; tyArray{'t}} }
   = it

prim ty_store_array2 {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["store"]{ nil; tyArray{'t} } }
   = it

(*!
 * @begin[doc]
 *
 * The typing rules for functions are straightforward.  Note that for
 * $<< polyFun{ x. 'f['x] } >>$ to be well-formed, $f$ must be a function.
 * These rules use the ``exp'' tag since in $<< lambda{ v. 'f['v] } >>$,
 * $f$ may be an expression.
 * @end[doc]
 *)

prim ty_store_lambda {| intro [] |} 'H 'a :
   sequent [mfir] { 'H >- type_eq{ 'arg_type; 'arg_type; large_type } } -->
   sequent [mfir] { 'H; a: var_def{ 'arg_type; no_def } >-
      has_type["exp"]{ 'f['a]; 'res_type } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{ lambda{ v. 'f['v] }; tyFun{ 'arg_type; 'res_type } } }
   = it

prim ty_store_polyFun1 {| intro [] |} 'H 'a :
   sequent [mfir] { 'H; a: ty_def{ small_type; no_def } >-
      has_type["exp"]{ polyFun{ y. 'f['a; 'y] }; 'ty['a] } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{ polyFun{ x. polyFun{ y. 'f['x; 'y] } };
                       tyAll{ t. 'ty['t] } } }
   = it

prim ty_store_polyFun2 {| intro [] |} 'H 'a :
   sequent [mfir] { 'H; a: ty_def{ small_type; no_def } >-
      has_type["exp"]{ lambda{ y. 'f['a; 'y] }; 'ty['a] } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{ polyFun{ x. lambda{ y. 'f['x; 'y] } };
                       tyAll{ t. 'ty['t] } } }
   = it

(*!
 * @begin[doc]
 *
 * ...
 * @end[doc]
 *)

(* XXX union store values should go here. *)

(* gagh the next rule requires a lot of work.
prim ty_store_union {| intro [] |} 'H :
   sequent [mfir] { 'H >-
      type_eq{ tyUnion{'ty_var; 'ty_list; singleton{number[i:n]}};
               large_type } } -->
   sequent [mfir] { 'H >-
      has_type["store"]{ union_val[i:n]{ 'ty_var; 'atom_list };
                         tyUnion{'ty_var; 'ty_list; singleton{number[i:n]}} }}
   = it
*)

(*!
 * @begin[doc]
 *
 * Raw data is represented abstractly as the value $<< raw_data >>$.
 * @end[doc]
 *)

prim ty_store_raw_data {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["store"]{ raw_data; tyRawData } }
   = it

(*!
 * @docoff
 *)
