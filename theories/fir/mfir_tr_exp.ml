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

open Base_dtactic

(**************************************************************************
 * Rules.
 **************************************************************************)

(*!
 * @begin[doc]
 * @rules
 *
 * Operationally, the term @tt[letAtom] binds @tt[atom] to @tt[v] in @tt[exp].
 * The expression has type @tt[ty2] if @tt[atom] has type @tt[ty1], and the
 * expression @tt[exp] has type @tt[ty2] under the assumption that @tt[v] has
 * type @tt[ty1]. The assumptions ensure that @tt[ty1] and @tt[ty2] are
 * well-formed types.
 * @end[doc]
 *)

prim ty_letAtom {| intro [] |} 'H 'a :
   sequent [mfir] { 'H >- has_type{ 'atom; 'ty1 } } -->
   sequent [mfir] { 'H; a: var_def{ 'ty1; no_def } >-
      has_type{ 'exp['a]; 'ty2 } } -->
   sequent [mfir] { 'H >-
      has_type{ letAtom{ 'ty1; 'atom; v. 'exp['v] }; 'ty2 } }
   = it

(*!
 * @docoff
 *)
