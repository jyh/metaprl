(*!
 * @begin[doc]
 * @module[M_prog]
 *
 * Lift closed function definitions to the top level.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003 Jason Hickey, Caltech
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
 * Author: Jason Hickey
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
extends M_ir
(*! @docoff *)

open M_ir
open M_util

open Mp_debug
open Printf

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermAddr
open Refiner.Refiner.RefineError

open Mp_resource
open Term_match_table

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent

open Var
open Perv

(************************************************************************
 * REDUCTION RESOURCE                                                   *
 ************************************************************************)

(*!
 * @begin[doc]
 * @resources
 *
 * @bf{The @Comment!resource[prog_resource]}
 *
 * The @tt{prog} resource provides a generic method for
 * defining @emph{CPS transformation}.  The @conv[progC] conversion
 * can be used to apply this evaluator.
 *
 * The implementation of the @tt{prog_resource} and the @tt[progC]
 * conversion rely on tables to store the shape of redices, together with the
 * conversions for the reduction.
 *
 * @docoff
 * @end[doc]
 *)
let resource prog =
   table_resource_info identity extract_data

let progTopC_env e =
   get_resource_arg (env_arg e) get_prog_resource

let progTopC = funC progTopC_env

let progC =
   repeatC (higherC progTopC)

(************************************************************************
 * Rewrites.
 *)

(*!
 * @begin[doc]
 * Swap a recursive definition with anything before it.
 * @end[doc]
 *)
prim_rw letrec_atom_fun :
   AtomFun{x. LetRec{R1. 'fields['R1]; R2. 'e['R2; 'x]}} <-->
   LetRec{R1. 'fields['R1]; R2. AtomFun{x. 'e['R2; 'x]}}

prim_rw letrec_let_atom :
    LetAtom{'a; v. LetRec{R1. 'fields['R1]; R2. 'e['R2; 'v]}} <-->
    LetRec{R1. 'fields['R1]; R2. LetAtom{'a; v. 'e['R2; 'v]}}

prim_rw letrec_let_tuple :
   LetTuple{'length; 'tuple; v. LetRec{R1. 'fields['R1]; R2. 'e['R2; 'v]}} <-->
   LetRec{R1. 'fields['R1]; R2. LetTuple{'length; 'tuple; v. 'e['R2; 'v]}}

prim_rw letrec_let_subscript :
   LetSubscript{'a1; 'a2; v. LetRec{R1. 'fields['R1]; R2. 'e['R2; 'v]}} <-->
   LetRec{R1. 'fields['R1]; R2. LetSubscript{'a1; 'a2; v. 'e['R2; 'v]}}

prim_rw letrec_let_closure :
   LetClosure{'f; 'a; v. LetRec{R1. 'fields['R1]; R2. 'e['R2; 'v]}} <-->
   LetRec{R1. 'fields['R1]; R2. LetClosure{'f; 'a; v. 'e['R2; 'v]}}

prim_rw letrec_if_true :
   If{'a; LetRec{R1. 'fields['R1]; R2. 'e1['R2]}; 'e2} <-->
   LetRec{R1. 'fields['R1]; R2. If{'a; 'e1['R2]; 'e2}}

prim_rw letrec_if_false :
   If{'a; 'e1; LetRec{R1. 'fields['R1]; R2. 'e2['R2]}} <-->
   LetRec{R1. 'fields['R1]; R2. If{'a; 'e1; 'e2['R2]}}

prim_rw letrec_fun_def :
   FunDef{'label; LetRec{R1. 'fields['R1]; R2. 'e['R2]}; 'rest} <-->
   LetRec{R1. 'fields['R1]; R2. FunDef{'label; 'e['R2]; 'rest}}

prim_rw letrec_fields_def :
   Fields{LetRec{R1. 'fields['R1]; R2. 'e['R2]}} <-->
   LetRec{R1. 'fields['R1]; R2. Fields{'e['R2]}}

prim_rw letrec_letrec :
   LetRec{R1. LetRec{R2. 'fields['R2]; R3. 'e1['R1; 'R3]}; R4. 'e2['R4]} <-->
   LetRec{R2. 'fields['R2]; R3. LetRec{R1. 'e1['R1; 'R3]; R4. 'e2['R4]}}

(*
 * Add all these rules to the prog resource.
 *)
let resource prog +=
    [<< AtomFun{x. LetRec{R1. 'fields['R1]; R2. 'e['R2; 'x]}} >>, letrec_atom_fun;
     << LetAtom{'a; v. LetRec{R1. 'fields['R1]; R2. 'e['R2; 'v]}} >>, letrec_let_atom;
     << LetTuple{'length; 'tuple; v. LetRec{R1. 'fields['R1]; R2. 'e['R2; 'v]}} >>, letrec_let_tuple;
     << LetSubscript{'a1; 'a2; v. LetRec{R1. 'fields['R1]; R2. 'e['R2; 'v]}} >>, letrec_let_subscript;
     << LetClosure{'f; 'a; v. LetRec{R1. 'fields['R1]; R2. 'e['R2; 'v]}} >>, letrec_let_closure;
     << If{'a; LetRec{R1. 'fields['R1]; R2. 'e1['R2]}; 'e2} >>, letrec_if_true;
     << If{'a; 'e1; LetRec{R1. 'fields['R1]; R2. 'e2['R2]}} >>, letrec_if_false;
     << FunDef{'label; LetRec{R1. 'fields['R1]; R2. 'e['R2]}; 'rest} >>, letrec_fun_def;
     << Fields{LetRec{R1. 'fields['R1]; R2. 'e['R2]}} >>, letrec_fields_def;
     << LetRec{R1. LetRec{R2. 'fields['R2]; R3. 'e1['R1; 'R3]}; R4. 'e2['R4]} >>, letrec_letrec]

(*
 * Wrap it all in a tactic.
 *)
let progT =
   rw progC 0

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
