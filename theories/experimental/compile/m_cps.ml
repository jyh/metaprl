(*!
 * @begin[doc]
 * @module[Top_conversionals]
 *
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
extends M_util
(*! @docoff *)

open M_ir
open M_util

open Mp_debug
open Printf

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError

open Mp_resource
open Simple_print
open Term_match_table

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent

(************************************************************************
 * REDUCTION RESOURCE                                                   *
 ************************************************************************)

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
 *
 * @begin[itemize]
 * @item{CPSRecordVar{R} represents the application of the record $R$ to
 *       the identify function.}
 *
 * @item{CPSFunVar{f} represents the application of the function $f$ to
 *       the identity function.}
 *
 * @item{
 *    @begin[verbatim]
 *    CPS{'cont; 'a; v. 'e['v]}
 *    @end[verbatim]
 *    means
 *    @begin[verbatim]
 *    let v = apply{'cont; 'a} in 'e['v]
 *    @end[verbatim]}
 *
 * @item{
 *    @begin[verbatim]
 *    CPS{'cont; 'e}
 *    @end[verbatim]
 *    is the CPS conversion of expression $e$ with continuation ${cont}$.
 *    The interpretation is as the application ${cont}@space{}e$.}
 *
 * @item{
 *    @begin[verbatim]
 *    CPS{cont. 'fields}
 *    @end[verbatim]
 *    is the CPS conversion of a record body.  We think of a record
 *    @begin[verbatim]
 *    { f1 = e1; ...; fn = en }
 *    @end[verbatim]
 *    as a function from labels to expressions (on label $f_i$, the function returns $e_i$).
 *    The CPS form is $@lambda l. @lambda c. CPS(c, {fields}(l))$.}
 * @end[itemize]
 * @end[doc]
 *)
declare CPSRecordVar{'R}
declare CPSFunVar{'f}

declare CPS{'a}
declare CPS{'cont; 'e}
declare CPS{cont. 'fields['cont]}

dform cps_record_var_df : CPSRecordVar{'R} =
   bf["CPSrec["] slot{'R} bf["]"]

dform cps_fun_var_df : CPSFunVar{'R} =
   bf["CPSfun["] slot{'R} bf["]"]

dform cps_atom_df : CPS{'a} =
   bf["CPS["] slot{'a} bf["]"]

dform cps_exp_df : CPS{'cont; 'e} =
   szone pushm[1] bf["CPS["] 'cont bf[";"] hspace 'e popm bf["]"] ezone

dform cps_fields_df : CPS{cont. 'e} =
   szone pushm[1] bf["CPS["] 'cont bf["."] hspace 'e popm bf["]"] ezone

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
prim_rw cps_atom_int : CPS{AtomInt[i:n]} <-->
   AtomInt[i:n]

prim_rw cps_atom_var : CPS{AtomVar{'v}} <-->
   AtomVar{'v}

prim_rw cps_atom_binop : CPS{AtomBinop{'op; 'a1; 'a2}} <-->
   AtomBinop{'op; CPS{'a1}; CPS{'a2}}

prim_rw cps_fun_var : CPS{CPSFunVar{'f}} <-->
   AtomVar{'f}

(*!
 * @begin[doc]
 * CPS transformation for expressions.
 * @end[doc]
 *)
prim_rw cps_let_atom : CPS{'cont; LetAtom{'a; v. 'e['v]}} <-->
   LetAtom{CPS{'a}; v. CPS{'cont; 'e['v]}}

prim_rw cps_let_pair : CPS{'cont; LetPair{'a1; 'a2; v. 'e['v]}} <-->
   LetPair{CPS{'a1}; CPS{'a2}; v. CPS{'cont; 'e['v]}}

prim_rw cps_let_subscript : CPS{'cont; LetSubscript{'a1; 'a2; v. 'e['v]}} <-->
   LetSubscript{CPS{'a1}; CPS{'a2}; v. CPS{'cont; 'e['v]}}

prim_rw cps_if : CPS{'cont; If{'a; 'e1; 'e2}} <-->
   If{CPS{'a}; CPS{'cont; 'e1}; CPS{'cont; 'e2}}

prim_rw cps_let_apply : CPS{'cont; LetApply{'a1; 'a2; v. 'e['v]}} <-->
   LetRec{R. FunDef{Label["g":t]; AtomFun{v. CPS{'cont; 'e['v]}};
             EndDef};
          R.
          LetFun{'R; Label["g":t]; g.
          TailCall{CPS{'a1}; 'g; CPS{'a2}}}}

(*!
 * @begin[doc]
 * Converting functions is the hard part.
 * @end[doc]
 *)
prim_rw cps_let_rec : CPS{'cont; LetRec{R1. 'fields['R1]; R2. 'e['R2]}} <-->
   LetRec{R1. CPS{cont. CPS{'cont; 'fields[CPSRecordVar{'R1}]}};
          R2. CPS{'cont; 'e[CPSRecordVar{'R2}]}}

prim_rw cps_fun_def : CPS{cont. CPS{'cont; FunDef{'label; AtomFun{v. 'e['v]}; 'rest}}} <-->
   FunDef{'label; AtomFun{cont. AtomFun{v. CPS{'cont; 'e['v]}}}; CPS{cont. CPS{'cont; 'rest}}}

prim_rw cps_end_def : CPS{cont. CPS{'cont; EndDef}} <-->
   EndDef

prim_rw cps_let_fun : CPS{'cont; LetFun{CPSRecordVar{'R}; 'label; f. 'e['f]}} <-->
   LetFun{'R; 'label; f. CPS{'cont; 'e[CPSFunVar{'f}]}}

prim_rw cps_return : CPS{'cont; Return{'a}} <-->
   TailCall{'cont; CPS{'a}}

prim_rw cps_tailcall : CPS{'cont; TailCall{CPSFunVar{'f}; 'a2}} <-->
   TailCall{'f; 'cont; CPS{'a2}}
(*! docoff *)

(*
 * Add all these rules to the CPS resource.
 *)
let resource cps +=
    [<< CPS{AtomInt[i:n]} >>, cps_atom_int;
     << CPS{AtomVar{'v}} >>, cps_atom_var;
     << CPS{AtomBinop{'op; 'a1; 'a2}} >>, cps_atom_binop;
     << CPS{CPSFunVar{'f}} >>, cps_fun_var;

     << CPS{'cont; LetAtom{'a; v. 'e['v]}} >>, cps_let_atom;
     << CPS{'cont; LetPair{'a1; 'a2; v. 'e['v]}} >>, cps_let_pair;
     << CPS{'cont; LetSubscript{'a1; 'a2; v. 'e['v]}} >>, cps_let_subscript;
     << CPS{'cont; If{'a; 'e1; 'e2}} >>, cps_if;
     << CPS{'cont; LetApply{'a1; 'a2; v. 'e['v]}} >>, cps_let_apply;

     << CPS{'cont; LetRec{R1. 'fields['R1]; R2. 'e['R2]}} >>, cps_let_rec;
     << CPS{cont. CPS{'cont; FunDef{'label; AtomFun{v. 'e['v]}; 'rest}}} >>, cps_fun_def;
     << CPS{cont. CPS{'cont; EndDef}} >>, cps_end_def;
     << CPS{'cont; LetFun{CPSRecordVar{'R}; 'label; f. 'e['f]}} >>, cps_let_fun;
     << CPS{'cont; Return{'a}} >>, cps_return;
     << CPS{'cont; TailCall{CPSFunVar{'f}; 'a2}} >>, cps_tailcall]

(*!
 * @begin[doc]
 * The program is compilable if the CPS version is compilable.
 * @end[doc]
 *)
interactive cps_prog :
   sequent [m] { 'H; cont: exp >-
      compilable{LetRec{R. FunDef{Label["init":t]; AtomFun{cont. CPS{'cont; 'e}}; EndDef};
                        R. LetFun{'R; Label["init":t]; init. TailCall{'init; AtomVar{'cont}}}}} } -->
   sequent [m] { 'H >- compilable{'e} }

(*
 * Toplevel CPS conversion tactic.
 *)
let cpsT =
   cps_prog thenT rw cpsC 0

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
