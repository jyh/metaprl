(*
 * The Mp_mc_deadcode module defines rewrites for deadcode
 * elimination of FIR programs.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
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
 * Email:  emre@its.caltech.edu
 *)

include Mp_mc_fir_exp
include Mp_mc_fir_eval

open Tactic_type.Conversionals

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(*
 * Expressions.
 *)

(* Primitive operations. *)

topval reduce_letUnop_deadcode : conv
topval reduce_letBinop_deadcode : conv

(* Allocation. *)

topval reduce_letAlloc_deadcode : conv

(* Subscripting. *)

topval reduce_letSubscript_deadcode : conv

(*************************************************************************
 * Automation.
 *************************************************************************)

topval firDeadcodeT : int -> tactic
