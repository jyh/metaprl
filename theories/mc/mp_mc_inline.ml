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
include Itt_list
include Itt_rfun
include Mp_mc_fir_base
include Mp_mc_fir_exp
include Mp_mc_fir_prog
(*! @docoff *)

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Top_conversionals
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

prim_rw reduce_extract_sym_func_pairs_1 :
   extract_sym_func_pairs{
      firProg{ 'file_info; 'import_list; 'export_list; 'tydef_list;
               'frame_list; 'ty_list; 'global_list; 'fundef_list }
   }
   <-->
   extract_sym_func_pairs{ 'fundef_list }

prim_rw reduce_extract_sym_func_pairs_2 :
   extract_sym_func_pairs{
      cons{ tableItem{ 'name; fundef{ 'debug_info; 'ty; 'func } };
            'tail
      }
   }
   <-->
   cons{ tableItem{ 'name; 'func }; extract_sym_func_pairs{ 'tail } }

prim_rw reduce_extract_sym_func_pairs_3 :
   extract_sym_func_pairs{ nil } <-->
   nil

(*
 * Retreiving a function body from the assoc. list created above.
 *)

prim_rw reduce_get_func_body_1 :
   get_func_body{ cons{ tableItem{ 'name; 'body }; 'tail }; 'name } <-->
   'body

prim_rw reduce_get_func_body_2 :
   get_func_body{ cons{ tableItem{ 'diff_name; 'body }; 'tail }; 'name } <-->
   get_func_body{ 'tail; 'name }

(*
 * Searching for a tailCall that we can inline.
 *)

(* Function definitions and lambda terms. *)

prim_rw reduce_inline_fundef :
   inline{ 'target; 'global_info; fundef{ 'debug_line; 'ty; 'body } } <-->
   fundef{ 'debug_line; 'ty; inline{ 'target; 'global_info; 'body } }

prim_rw reduce_inline_lambda :
   inline{ 'target; 'global_info; lambda{ x. 'b['x] } } <-->
   lambda{ x. inline{ 'target; 'global_info; 'b['x] } }

(* Primitive operations. *)

prim_rw reduce_inline_letUnop :
   inline{ 'target; 'global_info;
           letUnop{ 'ty; 'unop; 'atom; var. 'exp['var] } } <-->
   letUnop{ 'ty; 'unop; 'atom;
            var. inline{ 'target; 'global_info; 'exp['var] } }

prim_rw reduce_inline_letBinop :
   inline{ 'target; 'global_info;
           letBinop{ 'ty; 'binop; 'atom1; 'atom2; var. 'exp['var] } } <-->
   letBinop{ 'ty; 'binop; 'atom1; 'atom2;
             var. inline{ 'target; 'global_info; 'exp['var] } }

(* Function application. *)

prim_rw reduce_inline_tailCall_1 :
   inline{ tailCall{ 'lbl_1; 'name; 'args}; 'global_info;
           tailCall{ 'lbl_2; 'name; 'args} } <-->
   inline_tailCall_prep{ 'global_info; tailCall{ 'lbl_2; 'name; 'args} }

prim_rw reduce_inline_tailCall_2 :
   inline{ 'target; 'global_info; tailCall{ 'label; 'var; 'atom_list } } <-->
   tailCall{ 'label; 'var; 'atom_list }

(* Control. *)

prim_rw reduce_inline_matchExp :
   inline{ 'target; 'global_info;
           matchExp{ 'atom; 'matchCase_list } } <-->
   matchExp{ 'atom; inline{ 'target; 'global_info; 'matchCase_list } }

prim_rw reduce_inline_matchCase_list_ind :
   inline{ 'target; 'global_info;
           cons{ matchCase{ 'label; 'set; 'exp }; 'tail } } <-->
   cons{ matchCase{ 'label; 'set; inline{ 'target; 'global_info; 'exp } };
         inline{ 'target; 'global_info; 'tail } }

prim_rw reduce_inline_matchCase_list_nil :
   inline{ 'target; 'global_info; nil } <-->
   nil

(*
 * Expanding a tailCall so that we can further reduce it (inline it).
 *)

prim_rw reduce_inline_tailCall_prep :
   inline_tailCall_prep{ 'global_info; tailCall{ 'label; 'name; 'args } } <-->
   inline_tailCall{ get_func_body{ 'global_info; 'name }; 'args }

prim_rw reduce_inline_tailCall_real_1 :
   inline_tailCall{ 'body; cons{ 'arg; nil } } <-->
   apply{ 'body; 'arg }

prim_rw reduce_inline_tailCall_real_2 :
   inline_tailCall{ 'body; cons{ 'arg1; cons{ 'arg2; 'tail } } } <-->
   inline_tailCall{ apply{ 'body; 'arg1 }; cons{ 'arg2; 'tail } }

(*************************************************************************
 * Automation.
 *************************************************************************)

let firInlineGetGlobalInfoC =
   repeatC (higherC (applyAllC [

      reduce_extract_sym_func_pairs_1;
      reduce_extract_sym_func_pairs_2;
      reduce_extract_sym_func_pairs_3

   ] ))

let firInlineC =
   repeatC (higherC (applyAllC [

      reduce_get_func_body_1;
      reduce_get_func_body_2;

      reduce_inline_fundef;
      reduce_inline_lambda;
      reduce_inline_letUnop;
      reduce_inline_letBinop;
      reduce_inline_tailCall_1;
      reduce_inline_tailCall_2;
      reduce_inline_matchExp;
      reduce_inline_matchCase_list_ind;
      reduce_inline_matchCase_list_nil;

      reduce_inline_tailCall_prep;
      reduce_inline_tailCall_real_1;
      reduce_inline_tailCall_real_2

   ] ))

(*************************************************************************
 * Term operations.
 *************************************************************************)

let extract_sym_func_pairs_term = << extract_sym_func_pairs{ 't } >>
let extract_sym_func_pairs_opname = opname_of_term extract_sym_func_pairs_term
let is_extract_sym_func_pairs_term = is_dep0_term extract_sym_func_pairs_opname
let mk_extract_sym_func_pairs_term = mk_dep0_term extract_sym_func_pairs_opname
let dest_extract_sym_func_pairs_term =
   dest_dep0_term extract_sym_func_pairs_opname

let inline_term = << inline{ 'target; 'global_info; 'expr } >>
let inline_opname = opname_of_term inline_term
let is_inline_term = is_dep0_dep0_dep0_term inline_opname
let mk_inline_term = mk_dep0_dep0_dep0_term inline_opname
let dest_inline_term = dest_dep0_dep0_dep0_term inline_opname
