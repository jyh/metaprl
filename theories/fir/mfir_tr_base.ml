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

extends Mfir_bool
extends Mfir_int
extends Mfir_list
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
 * @modsubsection{Basic axioms}
 *
 * The @tt[truth_intro] rule allows proofs of side-conditions to be completed.
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
 * $<< small_type >>$ type to be used as a $<< large_type >>$ type.
 * @end[doc]
 *)

prim ty_small_as_large {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ 't1; 't2; small_type } } -->
   sequent [mfir] { 'H >- type_eq{ 't1; 't2; large_type } }
   = it

(*!
 * @begin[doc]
 *
 * The next rule says that if two types are equal in some kind $<< 'k >>$,
 * then they are equal equal in $<< polyKind{ 0; 'k } >>$.
 * @end[doc]
 *)

prim ty_polyKind_to_normal_kind {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ 't1; 't2; 'k } } -->
   sequent [mfir] { 'H >- type_eq{ 't1; 't2; polyKind{ 0; 'k } } }
   = it

(*!
 * @begin[doc]
 *
 * The next two rules are conviniences to check that the atoms in a list each
 * have the approriate type (given by a list of types).
 * @end[doc]
 *)

prim ty_atom_list1 {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom_list"]{ nil; nil } }
   = it

prim ty_atom_list2 {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'elt; 't } } -->
   sequent [mfir] { 'H >- has_type["atom_list"]{ 'tail; 'rest } } -->
   sequent [mfir] { 'H >-
      has_type["atom_list"]{ cons{ 'elt; 'tail }; cons{ 't; 'rest } } }
   = it

(*!
 * @begin[doc]
 *
 * The next two rules are conviniences to check that two lists of types are
 * pointwise equal in the specified kind.
 * @end[doc]
 *)

prim wf_ty_list1 {| intro [] |} 'H :
   sequent [mfir] { 'H >- wf_kind{ 'k } } -->
   sequent [mfir] { 'H >- type_eq_list{ nil; nil; 'k } }
   = it

prim wf_ty_list2 {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ 'h1; 'h2; 'k } } -->
   sequent [mfir] { 'H >- type_eq_list{ 't1; 't2; 'k } } -->
   sequent [mfir] { 'H >- type_eq_list{ cons{'h1; 't1}; cons{'h2; 't2}; 'k } }
   = it

(*!
 * @begin[doc]
 * @modsubsection{Kind well-formedness}
 *
 * Kind well-formedness if straightforward for $<< small_type >>$
 * and $<< large_type >>$.
 * @end[doc]
 *)

prim wf_small_type {| intro [] |} 'H :
   sequent [mfir] { 'H >- wf_kind{ small_type } }
   = it

prim wf_large_type {| intro [] |} 'H :
   sequent [mfir] { 'H >- wf_kind{ large_type } }
   = it

(*!
 * @begin[doc]
 *
 * The rules for the kind describing parametrized types are somewhat
 * more involved.  In the case of $<< small_type >>$ and $<< large_type >>$,
 * we disallow the case of $i = 0$.  The kind for union definitions, on the
 * other hand, must reflect some parametrization, even if there are
 * no parameters.
 * @end[doc]
 *)

prim wf_polyKind1 {| intro [] |} 'H :
   sequent [mfir] { 'H >- int_lt{ 0; 'i } } -->
   sequent [mfir] { 'H >- wf_kind{ polyKind{ 'i; small_type } } }
   = it

prim wf_polyKind2 {| intro [] |} 'H :
   sequent [mfir] { 'H >- int_lt{ 0; 'i } } -->
   sequent [mfir] { 'H >- wf_kind{ polyKind{ 'i; large_type } } }
   = it

prim wf_polyKind3 {| intro [] |} 'H :
   sequent [mfir] { 'H >- "and"{ int_le{ 0; 'i };
                                 int_le{ 0; number[j:n] } } } -->
   sequent [mfir] { 'H >- wf_kind{ polyKind{ 'i; union_type[j:n] } } }
   = it

(*!
 * @docoff
 *)
