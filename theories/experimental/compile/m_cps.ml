doc <:doc<
   @begin[spelling]
   CPS EMRE compilable op
   @end[spelling]

   @begin[doc]
   @module[M_cps]

   CPS conversion for the M language.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2003 Jason Hickey, Caltech

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
   @end[license]
>>

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>
extends M_ir
doc <:doc< @docoff >>

open M_util

open Refiner.Refiner.RefineError

open Term_match_table

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent
open Tactic_type.Rewrite

(************************************************************************
 * REDUCTION RESOURCE                                                   *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @resources

   @bf{The @Comment!resource[cps] resource}

   The @tt[cps] resource provides a generic method for
   defining @emph{CPS transformation}.  The @conv[cpsC] conversion
   can be used to apply this evaluator.

   The implementation of the @tt[cps] resource and the @tt[cpsC]
   conversion rely on tables to store the shape of redices, together with the
   conversions for the reduction.

   @end[doc]
   @docoff
>>
let resource (term * conv, conv) cps =
   table_resource_info extract_data

let process_cps_resource_rw_annotation = redex_and_conv_of_rw_annotation "cps"

let cpsTopC_env e =
   get_resource_arg (env_arg e) get_cps_resource

let cpsTopC = funC cpsTopC_env

let cpsC =
   repeatC (higherC cpsTopC)

(************************************************************************
 * CPS transformation
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @modsubsection{Application}

   Add an application that we will map through the program.
   This should be eliminated by the end of CPS conversion.

   @begin[itemize]
   @item{<<CPSRecordVar{'R}>> represents the application of the record $R$ to
         the identity function.}

   @item{<<CPSFunVar{'f}>> represents the application of the function $f$ to
         the identity function.}

   @item{<<CPS{'cont; 'e}>>
      is the CPS conversion of expression $e$ with continuation <<'cont>>.
      The interpretation is as the application $<<'cont>>@space<<'e>>$.}

   @item{<<CPS{cont. 'fields['cont]}>>
      is the CPS conversion of a record body.  We think of a record
      $@{ f_1 = e_1; ...; f_n = e_n @}$
      as a function from labels to expressions (on label $f_i$, the function returns $e_i$).
      The CPS form is $@lambda l. @lambda c. <<CPS{'c;'fields['l]}>>$.}

   @item{<<CPS{'a}>>
      is the conversion of the atom expression $a$ (which should be the same as $a$,
      unless $a$ includes function variables).}

   @end[itemize]
   @end[doc]
>>
declare CPSRecordVar{'R}
declare CPSFunVar{'f}

declare CPS{'cont; 'e}
declare CPS{cont. 'fields['cont]}
declare CPS{'a}

doc <:doc< @docoff >>

dform cps_record_var_df : CPSRecordVar{'R} =
   bf["CPSRecordVar["] slot{'R} bf["]"]

dform cps_fun_var_df : CPSFunVar{'f} =
   bf["CPSFunVar["] slot{'f} bf["]"]

dform cps_atom_df : CPS{'a} =
   bf["CPS["] slot{'a} bf["]"]

dform cps_exp_df : CPS{'cont; 'e} =
   szone pushm[1] bf["CPS["] 'cont bf[";"] hspace 'e popm bf["]"] ezone

dform cps_fields_df : CPS{cont. 'e} =
   szone pushm[1] bf["CPS["] 'cont bf["."] hspace 'e popm bf["]"] ezone

doc <:doc<
   @begin[doc]
   @modsubsection{Formalizing CPS conversion}

   CPS conversion work by transformation of function application.
   Each rewrite in the transformation preserves the operational
   semantics of the program.

   For atoms, the transformation is a no-op unless the atom is
   a function variable.  If so, the function must be partially applied.
   @end[doc]
>>
prim_rw cps_atom_true {| cps |} : CPS{AtomTrue} <-->
   AtomTrue

prim_rw cps_atom_false {| cps |} : CPS{AtomFalse} <-->
   AtomFalse

prim_rw cps_atom_int {| cps |} : CPS{AtomInt[i:n]} <-->
   AtomInt[i:n]

prim_rw cps_atom_var {| cps |} : CPS{AtomVar{'v}} <-->
   AtomVar{'v}

prim_rw cps_atom_binop {| cps |} : CPS{AtomBinop{'op; 'a1; 'a2}} <-->
   AtomBinop{'op; CPS{'a1}; CPS{'a2}}

prim_rw cps_atom_relop {| cps |} : CPS{AtomRelop{'op; 'a1; 'a2}} <-->
   AtomRelop{'op; CPS{'a1}; CPS{'a2}}

(* EMRE: so this rule expands (f (lambda x. x)) to f? *)
prim_rw cps_fun_var {| cps |} : CPS{CPSFunVar{'f}} <-->
   AtomVar{'f}

prim_rw cps_alloc_tuple_nil {| cps |} : CPS{AllocTupleNil} <-->
   AllocTupleNil

prim_rw cps_alloc_tuple_cons {| cps |} : CPS{AllocTupleCons{'a; 'rest}} <-->
   AllocTupleCons{CPS{'a}; CPS{'rest}}

prim_rw cps_arg_cons {| cps |} : CPS{ArgCons{'a; 'rest}} <-->
   ArgCons{CPS{'a}; CPS{'rest}}

prim_rw cps_arg_nil {| cps |} : CPS{ArgNil} <-->
   ArgNil

prim_rw cps_length {| cps |} : CPS{Length[i:n]} <-->
   Length[i:n]

doc <:doc<
   @begin[doc]
   CPS transformation for expressions.
   @end[doc]
>>
prim_rw cps_let_atom {| cps |} : CPS{'cont; LetAtom{'a; v. 'e['v]}} <-->
   LetAtom{CPS{'a}; v. CPS{'cont; 'e['v]}}

prim_rw cps_let_tuple {| cps |} : CPS{'cont; LetTuple{'length; 'tuple; v. 'e['v]}} <-->
   LetTuple{CPS{'length}; CPS{'tuple}; v. CPS{'cont; 'e['v]}}

prim_rw cps_let_subscript {| cps |} : CPS{'cont; LetSubscript{'a1; 'a2; v. 'e['v]}} <-->
   LetSubscript{CPS{'a1}; CPS{'a2}; v. CPS{'cont; 'e['v]}}

prim_rw cps_set_subscript {| cps |} :
   CPS{'cont; SetSubscript{'a1; 'a2; 'a3; 'e}}
   <-->
   SetSubscript{CPS{'a1}; CPS{'a2}; CPS{'a3}; CPS{'cont; 'e}}

prim_rw cps_if {| cps |} : CPS{'cont; If{'a; 'e1; 'e2}} <-->
   If{CPS{'a}; CPS{'cont; 'e1}; CPS{'cont; 'e2}}

(*
 * JYH BUG: please examine this.
 * I'm not sure I have it right.
 *
 * EMRE: I will believe this if
 *    (AtomVar{'f} (lambda x.x))
 * is equivalent to
 *    CPSFunVar{'f}
 *)
prim_rw cps_let_apply {| cps |} :
   CPS{'cont; LetApply{CPSFunVar{'f}; 'a2; v. 'e['v]}}
   <-->
   LetRec{R. FunDef{Label["g":t]; AtomFun{v. CPS{'cont; 'e['v]}};
             EndDef};
          R.
          LetFun{'R; Label["g":t]; g.
          TailCall{AtomVar{'f}; ArgCons{AtomVar{'g}; ArgCons{CPS{'a2}; ArgNil}}}}}

doc <:doc<
   @begin[doc]
   Converting functions is the hard part.
   @end[doc]
>>
prim_rw cps_let_rec {| cps |} : CPS{'cont; LetRec{R1. 'fields['R1]; R2. 'e['R2]}} <-->
   LetRec{R1. CPS{cont. CPS{'cont; 'fields[CPSRecordVar{'R1}]}};
          R2. CPS{'cont; 'e[CPSRecordVar{'R2}]}}

prim_rw cps_fields {| cps |} : CPS{cont. CPS{'cont; Fields{'fields['cont]}}} <-->
   Fields{CPS{cont. CPS{'cont; 'fields['cont]}}}

prim_rw cps_fun_def {| cps |} : CPS{cont. CPS{'cont; FunDef{'label; AtomFun{v. 'e['v]}; 'rest}}} <-->
   FunDef{'label; AtomFun{cont. AtomFun{v. CPS{'cont; 'e['v]}}}; CPS{cont. CPS{'cont; 'rest}}}

prim_rw cps_end_def {| cps |} : CPS{cont. CPS{'cont; EndDef}} <-->
   EndDef

prim_rw cps_initialize {| cps |} : CPS{'cont; Initialize{'e}} <-->
   Initialize{CPS{'cont; 'e}}

prim_rw cps_let_fun {| cps |} : CPS{'cont; LetFun{CPSRecordVar{'R}; 'label; f. 'e['f]}} <-->
   LetFun{'R; 'label; f. CPS{'cont; 'e[CPSFunVar{'f}]}}

prim_rw cps_return {| cps |} : CPS{'cont; Return{'a}} <-->
   TailCall{AtomVar{'cont}; ArgCons{CPS{'a}; ArgNil}}

prim_rw cps_tailcall {| cps |} : CPS{'cont; TailCall{CPSFunVar{'f}; 'args}} <-->
   TailCall{AtomVar{'f}; ArgCons{AtomVar{'cont}; CPS{'args}}}

prim_rw cps_fun_var_cleanup {| cps |} :
   AtomVar{CPSFunVar{'f}} <--> CPSFunVar{'f}
doc <:doc< @docoff >>

doc <:doc<
   @begin[doc]
   The program is compilable if the CPS version is compilable.
   @end[doc]
>>
prim cps_prog :
   sequent { <H>; cont: exp >-
      compilable{LetRec{R. FunDef{Label[".init":t]; AtomFun{cont. CPS{'cont; 'e}}; EndDef};
                        R. LetFun{'R; Label[".init":t]; init. Initialize{TailCall{AtomVar{'init}; ArgCons{AtomVar{'cont}; ArgNil}}}}}} } -->
   sequent { <H> >- compilable{'e} }

doc <:doc< @docoff >>

(*
 * Toplevel CPS conversion tactic.
 *)
let cpsT =
   cps_prog thenT rw cpsC 0

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
