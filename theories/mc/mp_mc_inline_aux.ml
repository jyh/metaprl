(*!
 * @begin[doc]
 * @theory[Mp_mc_deadcode]
 *
 * The @tt{Mp_mc_inline} module defines rewrites for
 * inlining of tailCall's in FIR programs.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * @email{emre@its.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Mp_mc_theory
(*! @docoff *)

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Top_conversionals
open Tactic_type.Conversionals
open Mp_mc_fir_eval

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

prim_rw reduce_get_func_body_1 :
   get_func_body {
      'target_tailCall;
      firProg{ 'file_info; 'import_list; 'export_list; 'tydef_list;
               'frame_list; 'ty_list; 'global_list; 'fundef_list }
   }
   <-->
   get_func_body{ 'target_tailCall; 'fundef_list }

prim_rw reduce_get_func_body_2 :
   get_func_body{
      tailCall_com[f:s]{ 'label; 'args };
      cons{ tableItem{ 'name2; fundef_com[f:s]{ 'debug_info; 'ty; 'func } };
            'tail
      }
   }
   <-->
   'func

prim_rw reduce_get_func_body_3 :
   get_func_body{ 'target_tailCall; cons{ 'tableItem; 'tail } } <-->
   get_func_body{ 'target_tailCall; 'tail }

(*
 * Expand a tailCall so that we can further reduce it (inline it).
 *)

prim_rw reduce_inline_tailCall_real_1 :
   inline_tailCall{ 'body; cons{ 'arg; nil } } <-->
   apply{ 'body; 'arg }

prim_rw reduce_inline_tailCall_real_2 :
   inline_tailCall{ 'body; cons{ 'arg1; cons{ 'arg2; 'tail } } } <-->
   inline_tailCall{ apply{ 'body; 'arg1 }; cons{ 'arg2; 'tail } }

prim_rw reduce_inline_tailCall_real_3 :
   inline_tailCall{ 'body; tailCall_com[str:s]{'label; 'args} } <-->
   inline_tailCall{ 'body; 'args }

(*************************************************************************
 * Automation.
 *************************************************************************)

let firInlineGetFuncBodyC =
   repeatC (higherC (applyAllC [
      reduce_get_func_body_1;
      reduce_get_func_body_2 orelseC reduce_get_func_body_3
   ] ))

let firInlineInlineTailCallC =
   repeatC (higherC (applyAllC [
      reduce_inline_tailCall_real_1;
      reduce_inline_tailCall_real_2;
      reduce_inline_tailCall_real_3
   ] ))

(*************************************************************************
 * Term operations.
 *************************************************************************)

let get_func_body_term = << get_func_body{ 'target_tailCall; 'prog } >>
let get_func_body_opname = opname_of_term get_func_body_term
let mk_get_func_body_term = mk_dep0_dep0_term get_func_body_opname

let inline_tailCall_term = << inline_tailCall{ 'body; 'args } >>
let inline_tailCall_opname = opname_of_term inline_tailCall_term
let mk_inline_tailCall_term = mk_dep0_dep0_term inline_tailCall_opname
