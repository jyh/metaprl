(*
 * The Mp_mc_const_elim module provides rewrites to perform
 * constant elimination (folding) in FIR programs.
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

include Itt_int_base
include Mp_mc_fir_ty
include Mp_mc_fir_exp

open Tactic_type.Conversionals

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(*
 * Basic facts about multiplication.
 *)

topval reduce_mulRawIntOp_opt1 : conv
topval reduce_mulRawIntOp_opt2 : conv
topval reduce_mulRawIntOp_opt3 : conv
topval reduce_mulRawIntOp_opt4 : conv

(*************************************************************************
 * Automation.
 *************************************************************************)

topval firConstElimC : conv
