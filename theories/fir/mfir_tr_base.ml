(*!
 * @begin[doc]
 * @module[Mfir_tr_base]
 *
 * The @tt[Mfir_tr_base] module defines the basic axioms of the FIR type
 * system.
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
 * Proofs of side-conditions require a proof of $<< "true" >>$, which we
 * take to be an axiom.
 * @end[doc]
 *)

prim truth_intro {| intro [] |} 'H :
   sequent [mfir] { 'H >- "true" }
   = it

(*!
 * @begin[doc]
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
 * @docoff
 *)
