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

open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermType
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError

open Mp_resource
open Var
open Mptop

open Simple_print
open Term_match_table

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent

(*
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
*)

(************************************************************************
 * CPS transformation
 ************************************************************************)

(*!
 * @begin[doc]
 * @modsubsection{CPS Application}
 *
 * Add an application that we will map through the program.
 * This should be eliminated by the end of CPS conversion.
 * @end[doc]
 *)
declare CPS{'e1; 'e2}

dform cps_df : CPS{'e1; 'e2} =
   `"CPS[" pushm[0] slot{'e1} popm `";" " " pushm[0] slot{'e2} popm `"]"

(*!
 * @begin[doc]
 * @modsubsection{CPS conversion}
 *
 * CPS conversion is expressed using inference rules.
 * @end[doc]
 *)
interactive cps_let_int 'H bind{x. 'A['x]} CPS{'cont; LetAtom{AtomInt[i:n]; v. 'e['v]}} :
   sequent [m] { 'H >- 'A[LetAtom{AtomInt[i:n]; v. CPS{'cont; 'e['v]}}] } -->
   sequent [m] { 'H >- 'A[CPS{'cont; LetAtom{AtomInt[i:n]; v. 'e['v]}}] }

interactive cps_let_binop 'H bind{x. 'A['x]} CPS{'cont; LetAtom{AtomBinop{'op; 'a1; 'a2}; v. 'e['v]}} :
   sequent [m] { 'H >- 'A[LetAtom{AtomBinop{'op; 'a1; 'a2}; v. CPS{'cont; 'e['v]}}] } -->
   sequent [m] { 'H >- 'A[CPS{'cont; LetAtom{AtomBinop{'op; 'a1; 'a2}; v. 'e['v]}}] }

interactive cps_let_fun 'H bind{x. 'A['x]} CPS{'cont; LetAtom{AtomFun{x. 'e1['x]}; f. 'e2['f]}} :
   sequent [m] { 'H >- 'A[LetAtom{AtomFun{g. AtomFun{x. CPS{'g; 'e1['x]}}}; f. CPS{'cont; 'e2[CPS{'f; AtomFun{z. 'z}}]}}] } -->
   sequent [m] { 'H >- 'A[CPS{'cont; LetAtom{AtomFun{x. 'e1['x]}; f. 'e2['f]}}] }

(*!
 * @begin[doc]
 * @modsubsection{Apply the transformation}
 *
 * We apply CPS transformation in two phases.
 * In the first phase, we transform the spine of the program.
 * @end[doc]
 *)
let cpsAddrT a p =
   let a = make_address a in
   let x = get_opt_var_arg "z" p in
   let x_term = mk_var_term x in
   let goal = Sequent.concl p in
   let apply = term_subterm goal a in
   let goal' = replace_subterm goal a x_term in
   let bind = mk_xbind_term x goal' in
   let addr = Sequent.hyp_count_addr p in
   let fail p =
      raise (RefineError ("M_cps.cpsAddrT", StringTermError ("no reduction for", apply)))
   in
      firstT [cps_let_int addr bind apply;
              cps_let_binop addr bind apply;
              cps_let_fun addr bind apply;
              fail] p

let cpsTestT a p =
   let a = make_address a in
   let x = get_opt_var_arg "z" p in
   let x_term = mk_var_term x in
   let goal = Sequent.concl p in
   let apply = term_subterm goal a in
   let goal' = replace_subterm goal a x_term in
   let bind = mk_xbind_term x goal' in
   let addr = Sequent.hyp_count_addr p in
   let fail p =
      raise (RefineError ("M_cps.cpsAddrT", StringTermError ("no reduction for", apply)))
   in
      cps_let_binop addr bind apply p

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
