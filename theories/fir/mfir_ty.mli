(*
 * The Mfir_ty module declares terms to represent the FIR type system.
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

extends Mfir_int
extends Mfir_list

open Tactic_type.Conversionals


(**************************************************************************
 * Declarations.
 **************************************************************************)

(*
 * Mutable types.
 *)

declare "mutable"
declare immutable
declare mutable_ty{ 'ty; 'flag }

(*
 * Type definitions.
 *)

declare tyDefPoly{ t. 'ty['t] }
declare frameSubField{ 'ty; 'num }
declare tyDefUnion{ 'cases }
declare tyDefDTuple{ 'ty_var }

(*
 * Numbers.
 *)

declare tyInt
declare tyEnum[i:n]
declare tyRawInt[precision:n, sign:s]
declare tyFloat[precision:n]

(*
 * Functions.
 *)

declare tyFun{ 'arg_type; 'res_type }

(*
 * Tuples.
 *)

declare tyUnion{ 'ty_var; 'ty_list; 'intset }
declare tyTuple[tc:s]{ 'ty_list }
declare tyDTuple{ 'ty_var; 'mtyl_option }
declare tyTag{ 'ty_var; 'mtyl }

(*
 * Other aggregates.
 *)

declare tyArray{ 'ty }
declare tyRawData
declare tyFrame{ 'ty_var; 'tyl }

(*
 * Polymorphism.
 *)

declare tyVar{ 'ty_var }
declare tyApply{ 'ty_var; 'ty_list }
declare tyExists{ t. 'ty['t] }
declare tyAll{ t. 'ty['t] }
declare tyProject[i:n]{ 'var }
