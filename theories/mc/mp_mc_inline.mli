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

include Itt_list
include Itt_rfun
include Mp_mc_fir_base
include Mp_mc_fir_exp
include Mp_mc_fir_prog

open Refiner.Refiner.Term
open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Extracting function bodies from an firProg.
 *)

declare extract_sym_func_pairs{ 't }
declare get_func_body{ 'global_info; 'name }

(*
 * Inlining tailCall's.
 *)

declare inline{ 'target; 'global_info; 'expr }
declare inline_tailCall_prep{ 'global_info; 'tailCall_target }
declare inline_tailCall{ 'body; 'args }

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(*
 * Creating an association list of ('name, 'func_body).
 *)

topval reduce_extract_sym_func_pairs_1 : conv
topval reduce_extract_sym_func_pairs_2 : conv
topval reduce_extract_sym_func_pairs_3 : conv

(*
 * Retreiving a function body from the assoc. list created above.
 *)

topval reduce_get_func_body_1 : conv
topval reduce_get_func_body_2 : conv

(*
 * Searching for a tailCall that we can inline.
 *)

topval reduce_inline_letUnop : conv
topval reduce_inline_letBinop : conv
topval reduce_inline_tailCall_1 : conv
topval reduce_inline_tailCall_2 : conv
topval reduce_inline_matchExp : conv
topval reduce_inline_matchCase_list_ind : conv
topval reduce_inline_matchCase_list_nil : conv

(*
 * Expanding a tailCall so that we can further reduce it (inline it).
 *)

topval reduce_inline_tailCall_prep : conv
topval reduce_inline_tailCall_real_1 : conv
topval reduce_inline_tailCall_real_2 : conv

(*************************************************************************
 * Automation.
 *************************************************************************)

topval firInlineGetGlobalInfoC : conv
topval firInlineC : conv

(*************************************************************************
 * Term operations.
 *************************************************************************)

val extract_sym_func_pairs_term : term
val is_extract_sym_func_pairs_term : term -> bool
val mk_extract_sym_func_pairs_term : term -> term
val dest_extract_sym_func_pairs_term : term -> term

val inline_term : term
val is_inline_term : term -> bool
val mk_inline_term : term -> term -> term -> term
val dest_inline_term : term -> term * term * term
