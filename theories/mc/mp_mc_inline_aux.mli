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

extends Mp_mc_theory

open Phobos_type
open Refiner.Refiner.Term
open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Extracting function bodies from an firProg.
 *)

declare get_func_body{ 'target_tailCall; 'prog }

(*
 * Inlining tailCall's.
 *)

declare inline_tailCall{ 'body; 'args }

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(*
 * Extract a function body from an firProg based on an inline target.
 *)

topval reduce_get_func_body_1 : conv
topval reduce_get_func_body_2 : conv
topval reduce_get_func_body_3 : conv

(*
 * Expanding a tailCall so that we can further reduce it (inline it).
 *)

topval reduce_inline_tailCall_real_1 : conv
topval reduce_inline_tailCall_real_2 : conv
topval reduce_inline_tailCall_real_3 : conv

(*************************************************************************
 * Automation.
 *************************************************************************)

topval firInlineGetFuncBodyC : conv
topval firInlineInlineTailCallC : conv

(*************************************************************************
 * Term operations.
 *************************************************************************)

val mk_get_func_body_term : term -> term -> term
val mk_inline_tailCall_term : term -> term -> term
