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
 * Swap FunDecl with any statements before it.
 * @end[doc]
 *)
prim_rw fundecl_atom_fun :
   AtomFun{x. FunDecl{f. 'e['f; 'x]}}
   <--> FunDecl{f. AtomFun{x. 'e['f; 'x]}}

prim_rw fundecl_let_atom :
    LetAtom{'a; v. FunDecl{f. 'e1['f; 'v]}}
    <--> FunDecl{f. LetAtom{'a; v. 'e1['f; 'v]}}

prim_rw fundecl_let_pair :
   LetPair{'a1; 'a2; v. FunDecl{f. 'e1['f; 'v]}}
   <--> FunDecl{f. LetPair{'a1; 'a2; v. 'e1['f; 'v]}}

prim_rw fundecl_let_subscript :
   LetSubscript{'a1; 'a2; v. FunDecl{f. 'e['f; 'v]}}
   <--> FunDecl{f. LetSubscript{'a1; 'a2; v. 'e['f; 'v]}}

prim_rw fundecl_if_true :
   If{'a; FunDecl{f. 'e1['f]}; 'e2}
   <--> FunDecl{f. If{'a; 'e1['f]; 'e2}}

prim_rw fundecl_if_false :
   If{'a; 'e1; FunDecl{f. 'e2['f]}}
   <--> FunDecl{f. If{'a; 'e1; 'e2['f]}}

prim_rw fundecl_fundef1 :
   FunDef{'f; FunDecl{g. 'e1['g]}; 'e2}
   <--> FunDecl{g. FunDef{'f; 'e1['g]; 'e2}}

prim_rw fundecl_fundef2 :
   FunDef{'f; 'e1; FunDecl{g. 'e2['g]}}
   <--> FunDecl{g. FunDef{'f; 'e1; 'e2['g]}}

prim_rw fundef_atom_fun :
   AtomFun{x. FunDef{'f; 'e1; 'e2['x]}}
   <--> FunDef{'f; 'e1; AtomFun{x. 'e2['x]}}

prim_rw fundef_let_atom :
   LetAtom{'a; v. FunDef{'f; 'e1; 'e2['v]}}
   <--> FunDef{'f; 'e1; LetAtom{'a; v. 'e2['v]}}

prim_rw fundef_let_pair :
   LetPair{'a1; 'a2; v. FunDef{'f; 'e1; 'e2['v]}}
   <--> FunDef{'f; 'e1; LetPair{'a1; 'a2; v. 'e2['v]}}

prim_rw fundef_let_subscript :
   LetSubscript{'a1; 'a2; v. FunDef{'f; 'e1; 'e2['v]}}
   <--> FunDef{'f; 'e1; LetSubscript{'a1; 'a2; v. 'e2['v]}}

prim_rw fundef_if_true :
   If{'a; FunDef{'f; 'e1; 'e2}; 'e3}
   <--> FunDef{'f; 'e1; If{'a; 'e2; 'e3}}

prim_rw fundef_if_false :
   If{'a; 'e1; FunDef{'f; 'e2; 'e3}}
   <--> FunDef{'f; 'e2; If{'a; 'e1; 'e3}}

prim_rw fundef_fundef :
   FunDef{'f; FunDef{'g; 'e1; 'e2}; 'e3}
   <--> FunDef{'f; 'e2; FunDef{'g; 'e1; 'e3}}

(*
 * Add all these rules to the prog resource.
 *)
let resource prog +=
    [<< AtomFun{x. FunDecl{f. 'e['f; 'x]}} >>, fundecl_atom_fun;
     << LetAtom{'a; v. FunDecl{f. 'e1['f; 'v]}} >>, fundecl_let_atom;
     << LetPair{'a1; 'a2; v. FunDecl{f. 'e1['f; 'v]}} >>, fundecl_let_pair;
     << LetSubscript{'a1; 'a2; v. FunDecl{f. 'e['f; 'v]}} >>, fundecl_let_subscript;
     << If{'a; FunDecl{f. 'e1['f]}; 'e2} >>, fundecl_if_true;
     << If{'a; 'e1; FunDecl{f. 'e2['f]}} >>, fundecl_if_false;
     << FunDef{'f; FunDecl{g. 'e1['g]}; 'e2} >>, fundecl_fundef1;
     << FunDef{'f; 'e1; FunDecl{g. 'e2['g]}} >>, fundecl_fundef2;

     << AtomFun{x. FunDef{'f; 'e1; 'e2['x]}} >>, fundef_atom_fun;
     << LetAtom{'a; v. FunDef{'f; 'e1; 'e2['v]}} >>, fundef_let_atom;
     << LetPair{'a1; 'a2; v. FunDef{'f; 'e1; 'e2['v]}} >>, fundef_let_pair;
     << LetSubscript{'a1; 'a2; v. FunDef{'f; 'e1; 'e2['v]}} >>, fundef_let_subscript;
     << If{'a; FunDef{'f; 'e1; 'e2}; 'e3} >>, fundef_if_true;
     << If{'a; 'e1; FunDef{'f; 'e2; 'e3}} >>, fundef_if_false;
     << FunDef{'f; FunDef{'g; 'e1; 'e2}; 'e3} >>, fundef_fundef]

(*!
 * @begin[doc]
 * Lift function past the turnstile.
 * @end[doc]
 *)
interactive hoist_fundecl 'H :
   sequent [m] { 'H; f : exp >- compilable{'e['f]} } -->
   sequent [m] { 'H >- compilable{FunDecl{f. 'e['f]}} }

interactive hoist_fundef 'H :
   sequent [m] { 'H; w: def{'f; 'e1} >- compilable{'e2} } -->
   sequent [m] { 'H >- compilable{FunDef{'f; 'e1; 'e2}} }

let hoistOnceT p =
   let addr = hyp_count_addr p in
      (hoist_fundecl addr orelseT hoist_fundef addr) p

let hoistT = repeatT hoistOnceT

(*
 * Wrap it all in a tactic.
 *)
let progT =
   rw progC 0 thenT hoistT

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
