(*
 * The Mfir_bool module implements meta-booleans for the FIR theory.
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
 * Constants.
 *)

declare "true"
declare "false"

(*
 * Connectives.
 *)

declare "or"{ 'bool1; 'bool2 }
declare "and"{ 'bool1; 'bool2 }
declare "not"{ 'boolean }

(*
 * Case analysis.
 *)

declare ifthenelse{ 'test; 'true_case; 'false_case }


(**************************************************************************
 * Rewrites.
 **************************************************************************)

topval reduce_and : conv
topval reduce_or : conv
topval reduce_not : conv
topval reduce_ifthenelse_true : conv
topval reduce_ifthenelse_false : conv
