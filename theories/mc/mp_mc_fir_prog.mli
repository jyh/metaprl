(*
 * The Mp_mc_fir_exp module defines terms to represent
 * FIR function definitions and program structures.
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

extends Base_theory

open Refiner.Refiner.Term

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

(*
 * Function definition.
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
 * An entire FIR program.
 *)

declare firProg{ 'file_info; 'import_list; 'export_list; 'tydef_list;
                 'frame_list; 'ty_list; 'global_list; 'fundef_list }

(*************************************************************************
 * Term operations.
 *************************************************************************)

(*
 * Global initializers.
 *)

val initAtom_term : term
val is_initAtom_term : term -> bool
val mk_initAtom_term : term -> term
val dest_initAtom_term : term -> term

val initAlloc_term: term
val is_initAlloc_term : term -> bool
val mk_initAlloc_term : term -> term
val dest_initAlloc_term : term -> term

(*
 * Function definition.
 *)

val fundef_term : term
val is_fundef_term : term -> bool
val mk_fundef_term : term -> term -> term -> term
val dest_fundef_term : term -> term * term * term
