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
declare CPS{'cont; 'a; v. 'e['v]}
declare CPS{'cont; 'e}

dform cps_atom_df : CPS{'cont; 'a; v. 'e} =
   szone pushm[1] bf["CPS["] 'cont bf[";"] " " 'a bf[";"] " " 'v `"." slot{'e} popm bf["]"] ezone

dform cps_exp_df : CPS{'cont; 'e} =
   szone pushm[1] bf["CPS["] 'cont bf[";"] hspace 'e popm bf["]"] ezone

(*!
 * @begin[doc]
 * @modsubsection{Formalizing CPS conversion}
 *
 * CPS conversion work by transformation of function application.
 * Each rewrite in the transformation preserves the operational
 * semantics of the program.
 *
 * For atoms, the transformation is a nop unless the atom is
 * a function var.  If so, the function must be partially applied.
 * @end[doc]
 *)
prim_rw cps_atom_int : CPS{'cont; AtomInt[i:n]; v. 'e['v]} <-->
   'e[AtomInt[i:n]]

prim_rw cps_atom_var : CPS{'cont; AtomVar{'v1}; v2. 'e['v2]} <-->
   'e['v1]

prim_rw cps_atom_binop : CPS{'cont; AtomBinop{'op; 'a1; 'a2}; v. 'e['v]} <-->
   CPS{'cont; 'a1; v1.
   CPS{'cont; 'a2; v2.
   LetAtom{AtomBinop{'op; 'v1; 'v2}; v. 'e['v]}}}

prim_rw cps_atom_fun_var : CPS{'cont; AtomFunVar{'f}; g. 'e['g]} <-->
   LetClosure{AtomFunVar{'f}; 'cont; g. 'e[AtomVar{'g}]}

(*!
 * @begin[doc]
 * CPS transformation for expressions.
 * @end[doc]
 *)
prim_rw cps_let_atom : CPS{'cont; LetAtom{'a; v. 'e['v]}} <-->
   CPS{'cont; 'a; v. CPS{'cont; 'e['v]}}

prim_rw cps_let_pair : CPS{'cont; LetPair{'a1; 'a2; v. 'e['v]}} <-->
   CPS{'cont; 'a1; v1.
   CPS{'cont; 'a2; v2.
   LetPair{'v1; 'v2; v.
   CPS{'cont; 'e['v]}}}}

prim_rw cps_let_subscript : CPS{'cont; LetSubscript{'a1; 'a2; v. 'e['v]}} <-->
   CPS{'cont; 'a1; v1.
   CPS{'cont; 'a2; v2.
   LetSubscript{'v1; 'v2;
   v. CPS{'cont; 'e['v]}}}}

prim_rw cps_if : CPS{'cont; If{'a; 'e1; 'e2}} <-->
   CPS{'cont; 'a; v.
   If{'v; CPS{'cont; 'e1}; CPS{'cont; 'e2}}}

prim_rw cps_let_apply : CPS{'cont; LetApply{'a1; 'a2; v. 'e['v]}} <-->
   FunDecl{g.
   FunDef{'g; AtomFun{v. CPS{'cont; 'e['v]}};
   CPS{'cont; 'a1; v1.
   CPS{'cont; 'a2; v2.
   TailCall{'v1; 'cont; 'v2}}}}}

prim_rw cps_return : CPS{'cont; Return{'a}} <-->
   CPS{'cont; 'a; v.
   TailCall{'cont; 'v}}

prim_rw cps_tailcall : CPS{'cont; TailCall{'a1; 'a2}} <-->
   CPS{'cont; 'a1; v1.
   CPS{'cont; 'a2; v2.
   TailCall{'v1; 'v2}}}

(*!
 * @begin[doc]
 * @modsubsection{CPS optimizations}
 *
 * The tailcall transformation may create an unecessary closure.
 * @end[doc]
 *)
prim_rw cps_opt_tailcall : LetClosure{'a1; 'a2; f. TailCall{AtomVar{'f}; 'a3}} <-->
   TailCall{'a1; 'a2; 'a3}

(*!
 * @begin[doc]
 * Functions get an extra argument.
 * @end[doc]
 *)
prim_rw cps_declare : CPS{'cont; FunDecl{f. 'e['f]}} <-->
   FunDecl{f. CPS{'cont; 'e['f]}}

prim_rw cps_define : CPS{'cont; FunDef{'f; AtomFun{x. 'e1['x]}; 'e2}} <-->
   FunDef{'f; AtomFun{cont. AtomFun{x. CPS{AtomVar{'cont}; 'e1['x]}}}; CPS{'cont; 'e2}}
(*! docoff *)

(*
 * Add all these rules to the CPS resource.
 *)
let resource cps +=
    [<< CPS{'cont; AtomInt[i:n]; v. 'e['v]} >>, cps_atom_int;
     << CPS{'cont; AtomVar{'v1}; v2. 'e['v2]} >>, cps_atom_var;
     << CPS{'cont; AtomBinop{'op; 'a1; 'a2}; v. 'e['v]} >>, cps_atom_binop;
     << CPS{'cont; AtomFunVar{'f}; g. 'e['g]} >>, cps_atom_fun_var;

     << CPS{'cont; LetAtom{'a; v. 'e['v]}} >>, cps_let_atom;
     << CPS{'cont; LetPair{'a1; 'a2; v. 'e['v]}} >>, cps_let_pair;
     << CPS{'cont; LetSubscript{'a1; 'a2; v. 'e['v]}} >>, cps_let_subscript;
     << CPS{'cont; If{'a; 'e1; 'e2}} >>, cps_if;
     << CPS{'cont; LetApply{'a1; 'a2; v. 'e['v]}} >>, cps_let_apply;
     << CPS{'cont; Return{'a}} >>, cps_return;
     << CPS{'cont; TailCall{AtomFunVar{'f}; 'e}} >>, cps_tailcall;

     << CPS{'cont; FunDecl{f. 'e['f]}} >>, cps_declare;
     << CPS{'cont; FunDef{'f; AtomFun{x. 'e1['x]}; 'e2}} >>, cps_define;

     << LetClosure{'a1; 'a2; f. TailCall{AtomVar{'f}; 'a3}} >>, cps_opt_tailcall]

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
