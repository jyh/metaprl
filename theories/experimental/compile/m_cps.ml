(*!
 * @begin[doc]
 *
 * @module[Top_conversionals]
 * CPS conversion for the M language.
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

open Mp_debug
open Printf

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError

open Mp_resource
open Simple_print
open Term_match_table

open Tactic_type.Conversionals
open Tactic_type.Sequent

(************************************************************************
 * REDUCTION RESOURCE                                                   *
 ************************************************************************)

(*
 * Display reductions.
 *)
let debug_cps =
   create_debug (**)
      { debug_name = "cps";
        debug_description = "display reductions during CPS conversion";
        debug_value = false
      }

(*!
 * @begin[doc]
 * @resources
 *
 * @bf{The @Comment!resource[cps_resource]}
 *
 * The @tt{cps} resource provides a generic method for
 * defining @emph{CPS transformation}.  The @conv[cpsC] conversion
 * can be used to apply this evaluator.
 *
 * The implementation of the @tt{cps_resource} and the @tt[cpsC]
 * conversion rely on tables to store the shape of redices, together with the
 * conversions for the reduction.
 *
 * @docoff
 * @end[doc]
 *)
let identity x = x

let extract_data tbl =
   let rw e =
      let t = env_term e in
      let conv =
         try
            (* Find and apply the right tactic *)
            if !debug_cps then
               eprintf "M_cps: lookup %a%t" debug_print t eflush;
            snd (Term_match_table.lookup tbl t)
         with
            Not_found ->
               raise (RefineError ("M_cps.extract_data", StringTermError ("no reduction for", t)))
      in
         if !debug_cps then
            eprintf "M_cps: applying %a%t" debug_print t eflush;
         conv
   in
      funC rw

let process_cps_resource_annotation name cvars vars args params mterm conv =
   match mterm with
      MetaIff (MetaTheorem t, _) ->
         (t, conv)
    | _ ->
         raise (RefineError ("M_cps.improve_resource_arg", StringError "not a simple rewrite"))

(*
 * Resource.
 *)
let resource cps =
   table_resource_info identity extract_data

let cpsTopC_env e =
   get_resource_arg (env_arg e) get_cps_resource

let cpsTopC = funC cpsTopC_env

let cpsC =
   repeatC (higherC cpsTopC)

(************************************************************************
 * CPS transformation
 ************************************************************************)

(*!
 * @begin[doc]
 * @modsubsection{Application}
 *
 * Add an application that we will map through the program.
 * This should be eliminated by the end of CPS conversion.
 * @end[doc]
 *)
declare Apply{'e1; 'e2}

prec prec_apply
prec prec_fun < prec_apply

dform apply_df : parens :: "prec"[prec_apply] :: Apply{'e1; 'e2} =
   slot["lt"]{'e1} `"@" slot["le"]{'e2}

(*!
 * @begin[doc]
 * @modsubsection{Formalizing CPS conversion}
 *
 * CPS conversion work by transformation of function application.
 * Each rewrite in the transformation preserves the operational
 * semantics of the program.
 * @end[doc]
 *)
prim_rw cps_let_atom : Apply{'cont; LetAtom{AtomInt[i:n]; v. 'e['v]}} <-->
   LetAtom{AtomInt[i:n]; v. Apply{'cont; 'e['v]}}

prim_rw cps_let_binop : Apply{'cont; LetAtom{AtomBinop{'op; 'a1; 'a2}; v. 'e['v]}} <-->
   LetAtom{AtomBinop{'op; 'a1; 'a2}; v. Apply{'cont; 'e['v]}}

prim_rw cps_let_fun : Apply{'cont; LetAtom{AtomFun{x. 'e1['x]}; f. 'e2['f]}} <-->
   LetAtom{AtomFun{cont. AtomFun{x. Apply{'cont; 'e1['x]}}}; f. Apply{'cont; 'e2[Apply{'f; AtomFun{x. 'x}}]}}

prim_rw cps_let_pair : Apply{'cont; LetPair{'a1; 'a2; v. 'e['v]}} <-->
   LetPair{'a1; 'a2; v. Apply{'cont; 'e['v]}}

prim_rw cps_let_subscript : Apply{'cont; LetSubscript{'a1; 'a2; v. 'e['v]}} <-->
   LetSubscript{'a1; 'a2; v. Apply{'cont; 'e['v]}}

prim_rw cps_return : Apply{'cont; Return{'a}} <-->
   TailCall{'cont; 'a}

(*
 * This rewrite is bogus for now.
 *)
prim_rw cps_tailcall : Apply{'cont; Apply{'f; AtomFun{x. 'x}}} <-->
   Apply{'f; 'cont}
(*! @docoff *)

let resource cps +=
    [<< Apply{'cont; LetAtom{AtomInt[i:n]; v. 'e['v]}} >>, cps_let_atom;
     << Apply{'cont; LetAtom{AtomBinop{'op; 'a1; 'a2}; v. 'e['v]}} >>, cps_let_binop;
     << Apply{'cont; LetAtom{AtomFun{x. 'e1['x]}; f. 'e2['f]}} >>, cps_let_fun;
     << Apply{'cont; LetPair{'a1; 'a2; v. 'e['v]}} >>, cps_let_pair;
     << Apply{'cont; LetSubscript{'a1; 'a2; v. 'e['v]}} >>, cps_let_subscript;
     << Apply{'cont; Return{'a}} >>, cps_return;
     << Apply{'cont; Apply{'f; AtomFun{x. 'x}}} >>, cps_tailcall]

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
