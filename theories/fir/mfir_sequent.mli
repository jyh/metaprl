(*
 * The Mfir_sequent module declares terms used FIR theory sequents.
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

open Tactic_type.Conversionals

(**************************************************************************
 * Declarations.
 **************************************************************************)

(*
 * Sequent tags.
 *)

declare mfir
declare it

(*
 * Kinds.
 *)

declare small_type
declare large_type
declare union_type[i:n]
declare polyKind[i:n]{ 'k }

(*
 * Store values.
 *)

declare polyFun{ t. 'f['t] }
declare lambda{ v. 'f['v] }
declare union_val[i:n]{ 'ty_var; 'atom_list }
declare raw_data

(*
 * Contexts.
 *)

declare ty_def{ 'k; 'def }
declare var_def{ 'ty; 'def }
declare global_def{ 'ty; 'def }
declare no_def

(*
 * Judgments.
 *)

declare wf_kind{ 'k }
declare type_eq{ 'ty1; 'ty2; 'k }
declare type_eq_list{ 'tyl1; 'tyl2; 'k }
declare has_type[str:s]{ 't; 'ty }
