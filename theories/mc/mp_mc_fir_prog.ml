(*!
 * @begin[doc]
 * @theory[Mp_mc_fir_exp]
 *
 * The @tt{Mp_mc_fir_exp} module defines terms to represent
 * FIR function definitions and program structures.
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
include Base_theory
(*! @docoff *)

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Mp_mc_base

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Global initializers.
 *)

declare initAtom{ 'atom }
declare initAlloc{ 'alloc_op }
declare initRawData{ 'int_precision; 'int_list }
declare initNameItem{ 'var; 'var_option }
declare initNames{ 'ty_var; 'initNameItem_list }

(*!
 * @begin[doc]
 *
 * Function definition
 * (Documentation incomplete.)
 * @end[doc]
 *)

declare fundef{ 'debug_line; 'ty; 'func }
declare fundef_com[f:s]{ 'debug_line; 'ty; 'func }

(*
 * Program globals.
 *)

declare global{ 'ty; 'init_exp }

(*
 * File information.
 *)

declare fileFC
declare fileNaml
declare fileJava
declare fileInfo{ 'string_dir; 'string_name; 'file_class }

(*
 * Imports.
 *)

declare argFunction
declare argPointer
declare argRawInt{ 'int_precision; 'int_signed }
declare argRawFloat{ 'float_precision }

declare importGlobal
declare importFun{ 'bool; 'import_arg_list }

declare import{ 'string; 'ty; 'import_info }

(*
 * Exports.
 *)

declare export{ 'string; 'ty }

(*
 * @begin[doc]
 *
 * An entire FIR program.
 * (Documentation incomplete.)
 * @end[doc]
 *)

declare firProg{ 'file_info; 'import_list; 'export_list; 'tydef_list;
                 'frame_list; 'ty_list; 'global_list; 'fundef_list }

(*! @docoff *)

(*************************************************************************
 * Display forms.
 *************************************************************************)

(*
 * Global initializers.
 *)

dform initAtom_df : except_mode[src] ::
   initAtom{ 'atom } =
   `"InitAtom(" slot{'atom} `")"
dform initAlloc_df : except_mode[src] ::
   initAlloc{ 'alloc_op } =
   `"InitAlloc(" slot{'alloc_op} `")"
dform initRawData_df : except_mode[src] ::
   initRawData{ 'int_precision; 'int_list } =
   `"InitRawData(" slot{'int_precision} `"," slot{'int_list} `")"
dform initNameItem_df : except_mode[src] ::
   initNameItem{ 'var; 'var_option } =
   `"InitNameItem(" slot{'var} `"," slot{'var_option} `")"
dform initNames_df : except_mode[src] ::
   initNames{ 'ty_var; 'initNameItem_list } =
   `"InitNames(" slot{'ty_var} `"," slot{'initNameItem_list} `")"

(*
 * Function definition.
 *)

dform fundef_df : except_mode[src] ::
   fundef{ 'debug_line; 'ty; 'func } =
   `"Fundef(" slot{'debug_line} `"," slot{'ty} `"," slot{'func} `")"

(*
 * Program globals.
 *)

dform global_df : except_mode[src] ::
   global{ 'ty; 'init_exp } =
   `"Global(" slot{'ty} `"," slot{'init_exp} `")"

(*
 * File information.
 *)

dform fileFC_df : except_mode[src] ::
   fileFC =
   `"FileFC"
dform fileNaml_df : except_mode[src] ::
   fileNaml =
   `"FileNaml"
dform fileJava_df : except_mode[src] ::
   fileJava =
   `"FileJava"
dform fileInfo_df : except_mode[src] ::
   fileInfo{ 'string_dir; 'string_name; 'file_class } =
   `"FileInfo(" slot{'string_dir} `"," slot{'string_name} `","
   slot{'file_class} `")"

(*
 * Imports.
 *)

dform argFunction_df : except_mode[src] ::
   argFunction =
   `"ArgFunction"
dform argPointer_df : except_mode[src] ::
   argPointer =
   `"ArgPointer"
dform argRawInt_df : except_mode[src] ::
   argRawInt{ 'int_precision; 'int_signed } =
   `"ArgRawInt(" slot{'int_precision} `"," slot{'int_signed} `")"
dform argRawFloat_df : except_mode[src] ::
   argRawFloat{ 'float_precision } =
   `"ArgRawFloat(" slot{'float_precision} `")"

dform importGlobal_df : except_mode[src] ::
   importGlobal =
   `"ImportGlobal"
dform importFun_df : except_mode[src] ::
   importFun{ 'bool; 'import_arg_list } =
   `"ImportFun(" slot{'bool} `"," slot{'import_arg_list} `")"

dform import_df : except_mode[src] ::
   import{ 'string; 'ty; 'import_info } =
   `"Import(" slot{'string} `"," slot{'ty} `"," slot{'import_info} `")"

(*
 * Exports.
 *)

dform export_df : except_mode[src] ::
   export{ 'string; 'ty } =
   `"Export(" slot{'string} `"," slot{'ty} `")"

(*
 * An entire FIR program.
 *)

dform firProg_df : except_mode[src] ::
   firProg{ 'file_info; 'import_list; 'export_list; 'tydef_list;
            'frame_list; 'ty_list; 'global_list; 'fundef_list } =
   `"FirProg(" slot{'file_info} `"," slot{'import_list} `","
   slot{'export_list} `"," slot{'tydef_list} `","
   slot{'frame_list} `"," slot{'ty_list} `","
   slot{'global_list} `"," slot{'fundef_list} `")"

(*************************************************************************
 * Term operations.
 *************************************************************************)

(*
 * Global initializers.
 *)

let initAtom_term = << initAtom{ 'atom } >>
let initAtom_opname = opname_of_term initAtom_term
let is_initAtom_term = is_dep0_term initAtom_opname
let mk_initAtom_term = mk_dep0_term initAtom_opname
let dest_initAtom_term = dest_dep0_term initAtom_opname

let initAlloc_term = << initAlloc{ 'alloc_op } >>
let initAlloc_opname = opname_of_term initAlloc_term
let is_initAlloc_term = is_dep0_term initAlloc_opname
let mk_initAlloc_term = mk_dep0_term initAlloc_opname
let dest_initAlloc_term = dest_dep0_term initAlloc_opname

(*
 * Function definition.
 *)

let fundef_term = << fundef{ 'debug_line; 'ty; 'func } >>
let fundef_opname = opname_of_term fundef_term
let is_fundef_term = is_dep0_dep0_dep0_term fundef_opname
let mk_fundef_term = mk_dep0_dep0_dep0_term fundef_opname
let dest_fundef_term = dest_dep0_dep0_dep0_term fundef_opname
