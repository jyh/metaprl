(*!
 * @begin[doc]
 * @theory[Mp_mc_fir_phobos]
 *
 * The @tt[Mp_mc_fir_phobos] module provides rules to convert
 * the FIR-like terms from the Phobos FIR implementation to the
 * term language used in this theory.
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
 * Copyright (C) 2002 Adam Granicz, Caltech
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
 * Author: Adam Granicz
 * @email{granicz@cs.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Base_theory
include Itt_theory
include Mp_mc_fir_exp
include Mp_mc_fir_phobos_exp
(*! @docoff *)

open Opname
open Refiner.Refiner.Term
open Refiner.Refiner.TermType
open Refiner.Refiner.RefineError
open Top_conversionals

(*
 * This is test code for input forms.
 * I'm just placing it here to show the example.
 * You won't need to use the magic term explicitly.
 *)
declare junk{'e}
declare magic[x:s]{'t}

iform magic_test : junk{magic[x:s]{'e}} <--> lambda{x. 'e}

let test_rewrite = apply_rewrite (Mp_resource.theory_bookmark "Mp_mc_fir_phobos")

(*
 * Basic rewrites including variables, strings, and numbers.
 * Currently, these need some work.
 * We need to take care of extended identifiers.
 *)
(*
prim_rw fir_variable :
   variable[v:s] <--> variable[v:v]

prim_rw fir_string :
   string[s:s] <--> token[s:t]

prim_rw fir_number :
   number[n:s] <--> number[n:n]
*)

(*
 * Rewrites for expressions.
 *)
prim_rw fir_cps_unop :
   cons{letUnop[v:s]{'ty; 'unop; 'a}; 'list} <-->
      Mp_mc_fir_exp!letUnop{'ty; 'unop; 'a; v. 'list}

prim_rw fir_cps_binop :
   cons{letBinop[v:s]{'ty; 'binop; 'a1; 'a2}; 'list} <-->
      Mp_mc_fir_exp!letBinop{'ty; 'binop; 'a1; 'a2; v. 'list}

prim_rw fir_cps_ext_call :
   cons{letExt[v:s]{'ty1; 'filename; 'ty2; 'args}; 'list} <-->
      Mp_mc_fir_exp!letExt{'ty1; 'filename; 'ty2; 'args; v. 'list}

prim_rw fir_cps_call :
   cons{call{'label; 'f; 'args}; 'list} <-->
      Mp_mc_fir_exp!call{'label; 'f; 'args; 'list}

prim_rw fir_cps_alloc :
   cons{letAlloc[v:s]{'op}; 'list} <-->
      Mp_mc_fir_exp!letAlloc{'op; v. 'list}

prim_rw fir_cps_let_subscript :
   cons{letSubscript[v:s]{'op; 'ty; 'v2; 'a}; 'list} <-->
      Mp_mc_fir_exp!letSubscript{'op; 'ty; 'v2; 'a; v. 'list}

prim_rw fir_cps_set_subscript :
   cons{setSubscript{'op; 'label; 'var; 'a1; 'ty; 'a2}; 'list} <-->
      Mp_mc_fir_exp!setSubscript{'op; 'label; 'var; 'a1; 'ty; 'a2; 'list}

prim_rw fir_cps_global :
   cons{setGlobal{'sub_value; 'label; 'var; 'ty; 'a}; 'list} <-->
      Mp_mc_fir_exp!setGlobal{'sub_value; 'label; 'var; 'ty; 'a; 'list}

prim_rw fir_cps_memcpy :
   cons{memcpy{'op; 'label; 'v1; 'a1; 'v2; 'a2; 'a3}; 'list} <-->
      Mp_mc_fir_exp!memcpy{'op; 'label; 'v1; 'a1; 'v2; 'a2; 'a3; 'list}

prim_rw fir_cps_assert :
   cons{assertExp{'var; 'pred}; 'list} <-->
      Mp_mc_fir_exp!assertExp{'var; 'pred; 'list}

prim_rw fir_cps_debug :
   cons{debug{'debug_info}; 'list} <-->
      Mp_mc_fir_exp!debug{'debug_info; 'list}

(*
 * Tailcalls and the like.
 * Technically, these can only be at the end of the list.
 *)
prim_rw fir_cps_tailcall :
   cons{tailCall{'label; 'f; 'params}; nil} <-->
      Mp_mc_fir_exp!tailCall{'label; 'f; 'params}

prim_rw fir_cps_special_call :
   cons{specialCall{'label; 'tailop}; nil} <-->
      Mp_mc_fir_exp!specialCall{'label; 'tailop}

prim_rw fir_cps_match :
   cons{matchExp{'a; 'list}; nil} <-->
      Mp_mc_fir_exp!matchExp{'a; 'list}

prim_rw fir_cps_typecase :
   cons{typeCase{'a1; 'a2; 'v1; 'v2; 'e1; 'e2}; nil} <-->
      Mp_mc_fir_exp!typeCase{'a1; 'a2; 'v1; 'v2; 'e1; 'e2}

(*
 * Automation.
 *)
let preFirToFirC =
   repeatC (higherC (applyAllC [
(*
      fir_variable;
      fir_string;
      fir_number;
*)
      fir_cps_unop;
      fir_cps_binop;
      fir_cps_ext_call;
      fir_cps_call;
      fir_cps_alloc;
      fir_cps_let_subscript;
      fir_cps_set_subscript;
      fir_cps_global;
      fir_cps_memcpy;
      fir_cps_assert;
      fir_cps_debug;
      fir_cps_tailcall;
      fir_cps_special_call;
      fir_cps_match;
      fir_cps_typecase
   ]))
