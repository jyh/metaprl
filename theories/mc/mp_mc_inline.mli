(*
 * The Mp_mc_inline module defines rewrites for
 * inlining of tailCall's in FIR programs.
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

include Mp_mc_theory
include Mp_mc_inline_aux

open Phobos_type
open Refiner.Refiner.Term
open Tactic_type.Conversionals

(*************************************************************************
 * Automation.
 *************************************************************************)

(*
 * Given a program term, and a list of targets to inline, this conversional
 * will inline all the targets it can find, until a fix point is
 * reached.  It's recommended that the inline targets not be recursive
 * function calls, unless the recursive function calls eventually
 * terminate.
 *)

val firInlineC : term -> mp_pre_term list -> conv
