(*!
 * @begin[doc]
 * @module[Mfir_tr_types]
 *
 * The @tt[Mfir_tr_types] module defines type equality judgments, which are
 * used to determine the well-formedness of FIR types.
 * @end[doc]
 *
 * ------------------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.  Additional
 * information about the system is available at
 * http://www.metaprl.org/
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
 * @email{emre@cs.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)

extends Base_theory
extends Mfir_basic
extends Mfir_ty
extends Mfir_exp
extends Mfir_sequent

(*!
 * @docoff
 *)

open Tactic_type
open Tactic_type.Tacticals
open Base_auto_tactic
open Base_dtactic
open Mfir_auto

(**************************************************************************
 * Rules.
 **************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Basic types}
 *
 * The equality judgment for $<< tyInt >>$ is straightforward.
 * @end[doc]
 *)

prim wf_tyInt {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ tyInt; tyInt; small_type } }
   = it

(*!
 * @begin[doc]
 *
 * Two enumeration types are equal if they have the same parameter $i$, and if
 * $i$ is within the allowed range of values.  This latter restriction assists
 * the Mojave compiler's garbage collector in differentiating between
 * enumeration constants and pointers.
 * @end[doc]
 *)

prim wf_tyEnum {| intro [] |} 'H :
   sequent [mfir] { 'H >- member{ number[i:n]; enum_max } } -->
   sequent [mfir] { 'H >- type_eq{ tyEnum[i:n]; tyEnum[i:n]; small_type } }
   = it

(*!
 * @begin[doc]
 *
 * The equality judgments for the types of raw integers and floating point
 * values are straightforward. Note that $<< tyRawInt[p:n, sign:s] >>$ and
 * $<< tyFloat[p:n] >>$ cannot be used as $<< small_type >>$ types.
 * @end[doc]
 *)

prim wf_tyRawInt_signed {| intro [] |} 'H :
   sequent [mfir] { 'H >-
      "or"{ int_eq{ number[p:n]; 8 };
      "or"{ int_eq{ number[p:n]; 16 };
      "or"{ int_eq{ number[p:n]; 32 };
            int_eq{ number[p:n]; 64 } } } } } -->
   sequent [mfir] { 'H >- type_eq{ tyRawInt[p:n, "signed"];
                                   tyRawInt[p:n, "signed"];
                                   large_type } }
   = it

prim wf_tyRawInt_unsigned {| intro [] |} 'H :
   sequent [mfir] { 'H >-
      "or"{ int_eq{ number[p:n]; 8 };
      "or"{ int_eq{ number[p:n]; 16 };
      "or"{ int_eq{ number[p:n]; 32 };
            int_eq{ number[p:n]; 64 } } } } } -->
   sequent [mfir] { 'H >- type_eq{ tyRawInt[p:n, "unsigned"];
                                   tyRawInt[p:n, "unsigned"];
                                   large_type } }
   = it

prim wf_tyFloat {| intro [] |} 'H :
   sequent [mfir] { 'H >-
      "or"{ int_eq{ number[p:n]; 32 };
      "or"{ int_eq{ number[p:n]; 64 };
            int_eq{ number[p:n]; 80 } } } } -->
   sequent [mfir] { 'H >- type_eq{ tyFloat[p:n];
                                   tyFloat[p:n];
                                   large_type } }
   = it

(*!
 * @begin[doc]
 *
 * Two function types are equal if their arguments types are equal, and if
 * the types of their return values are equal.
 * @end[doc]
 *)

prim wf_tyFun {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ 'a1; 'a2; large_type } } -->
   sequent [mfir] { 'H >- type_eq{ 'r1; 'r2; large_type } } -->
   sequent [mfir] { 'H >- type_eq{ tyFun{ 'a1; 'r1 };
                                   tyFun{ 'a2; 'r2 };
                                   small_type } }
   = it

(*!
 * @begin[doc]
 *
 * Two union types are equal if they name the same union definition, select
 * the same subset of cases, and instantiate the definition at the same types.
 * The well-formedness of the sequent ensures that the definition is
 * well-formed.  Note that we need two rules to distinguish between the
 * cases in which $tv$ is a polymorphic union definition, and when it isn't.
 * @end[doc]
 *)

(*
 * Non-polymorphic case.
 *)

prim wf_tyUnion1 'H 'J :
   (* Types the unions are instantiated at should be equal. *)
   sequent [mfir] { 'H; tv: ty_def{ union_type[j:n]; 'def }; 'J['tv] >-
      type_eq_list{ 'tyl1; 'tyl2; small_type } } -->

   (* The subset of cases should actually be a subset. *)
   sequent [mfir] { 'H; tv: ty_def{ union_type[j:n]; 'def }; 'J['tv] >-
      subset{ 'intset1; intset{ interval{ 0; (number[j:n] -@ 1) } } } } -->

   (* The subset of cases should be equal. *)
   sequent [mfir] { 'H; tv: ty_def{ union_type[j:n]; 'def }; 'J['tv] >-
      set_eq{ 'intset1; 'intset2 } } -->

   (* Then the two tyUnion's are equal. *)
   sequent [mfir] { 'H; tv: ty_def{ union_type[j:n]; 'def }; 'J['tv] >-
      type_eq{ tyUnion{ 'tv; 'tyl1; 'intset1 };
               tyUnion{ 'tv; 'tyl2; 'intset2 };
               small_type } }
   = it

(*
 * Polymorphic case.
 *)

prim wf_tyUnion2 'H 'J :
   (* Types the unions are instantiated at should be equal. *)
   sequent [mfir] { 'H;
                    tv: ty_def{ polyKind[i:n]{ union_type[j:n] }; 'def };
                    'J['tv] >-
      type_eq_list{ 'tyl1; 'tyl2; small_type } } -->

   (* The subset of cases should actually be a subset. *)
   sequent [mfir] { 'H;
                    tv: ty_def{ polyKind[i:n]{ union_type[j:n] }; 'def };
                    'J['tv] >-
      subset{ 'intset1; intset{ interval{ 0; (number[j:n] -@ 1) } } } } -->

   (* The subset of cases should be equal. *)
   sequent [mfir] { 'H;
                    tv: ty_def{ polyKind[i:n]{ union_type[j:n] }; 'def };
                    'J['tv] >-
      set_eq{ 'intset1; 'intset2 } } -->

   (* Then the two tyUnion's are equal. *)
   sequent [mfir] { 'H;
                    tv: ty_def{ polyKind[i:n]{ union_type[j:n] }; 'def };
                    'J['tv] >-
      type_eq{ tyUnion{ 'tv; 'tyl1; 'intset1 };
               tyUnion{ 'tv; 'tyl2; 'intset2 };
               small_type } }
   = it

(*!
 * @docoff
 *)

let d_wf_tyUnion1 i p =
   let j, k = Sequent.hyp_indices p i in
      wf_tyUnion1 j k p

let d_wf_tyUnion2 i p =
   let j, k = Sequent.hyp_indices p i in
      wf_tyUnion2 j k p

let resource auto += [{
   auto_name = "d_wf_tyUnion1";
   auto_prec = fir_auto_prec;
   auto_tac = onSomeHypT d_wf_tyUnion1;
   auto_type = AutoNormal
}; {
   auto_name = "d_wf_tyUnion2";
   auto_prec = fir_auto_prec;
   auto_tac = onSomeHypT d_wf_tyUnion2;
   auto_type = AutoNormal
}]

(*!
 * @begin[doc]
 *
 * Two tuple types are equal if they are the same kind of tuple, and their
 * projections are pointwise equal.  Note that box tuples must have arity one.
 * @end[doc]
 *)

prim wf_tyTuple_box {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ 't1; 't2; large_type } } -->
   sequent [mfir] { 'H >- type_eq{ tyTuple["box"]{ cons{ 't1; nil } };
                                   tyTuple["box"]{ cons{ 't2; nil } };
                                   small_type } }
   = it

prim wf_tyTuple_normal {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq_list{ 'tyl1; 'tyl2; large_type } } -->
   sequent [mfir] { 'H >- type_eq{ tyTuple["normal"]{ 'tyl1 };
                                   tyTuple["normal"]{ 'tyl2 };
                                   small_type } }
   = it

(*!
 * @begin[doc]
 *
 * Two array types are equal if their element types are equal.
 * @end[doc]
 *)

prim wf_tyArray {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ 't1; 't2; large_type } } -->
   sequent [mfir] { 'H >- type_eq{ tyArray{'t1}; tyArray{'t2}; small_type } }
   = it

(*!
 * @begin[doc]
 *
 * The rawdata type $<< tyRawData >>$ is used to represent data without
 * strict typing rules.
 * @end[doc]
 *)

prim wf_tyRawData {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ tyRawData; tyRawData; small_type } }
   = it

(*!
 * @begin[doc]
 * @modsubsection{Polymorphism}
 *
 * Two type variables are equal if they name the same variable, and the
 * variable is declared in the context with the specified kind.
 * @end[doc]
 *)

(* BUG: Is exact equality really the way to go? *)

prim wf_tyVar 'H 'J :
   sequent [mfir] { 'H; tv: ty_def{ 'k; 'def}; 'J['tv] >-
      type_eq{ tyVar{ 'tv }; tyVar{ 'tv }; 'k } }
   = it

(*!
 * @docoff
 *)

let d_wf_tyVar i p =
   let j, k = Sequent.hyp_indices p i in
      wf_tyVar j k p

let resource auto += {
   auto_name = "d_wf_tyVar";
   auto_prec = fir_auto_prec;
   auto_tac = onSomeHypT d_wf_tyVar;
   auto_type = AutoNormal
}

(*!
 * @begin[doc]
 *
 * Two type applications are equal if the name the same parametrized type,
 * and instantiate that type at equal lists of types.
 * @end[doc]
 *)

prim wf_tyApply1 'H 'J :
   sequent [mfir] { 'H; tv: ty_def{ polyKind[i:n]{ 'k }; 'def }; 'J['tv] >-
      int_eq{ number[i:n]; length{ 'tyl1 } } } -->
   sequent [mfir] { 'H; tv: ty_def{ polyKind[i:n]{ 'k }; 'def }; 'J['tv] >-
      type_eq_list{ 'tyl1; 'tyl2; small_type } } -->
   sequent [mfir] { 'H; tv: ty_def{ polyKind[i:n]{ 'k }; 'def }; 'J['tv] >-
      type_eq{ tyApply{ 'tv; 'tyl1 };
               tyApply{ 'tv; 'tyl2 };
               'k } }
   = it

(*!
 * @begin[doc]
 *
 * If the context contains a definition, we can expand a type application.
 * @end[doc]
 *)

prim wf_tyApply2 'H 'J :
   sequent [mfir] { 'H;
                    tv: ty_def{ polyKind[i:n]{'k}; tyDefPoly{t. 'ty['t]} };
                    'J['tv] >-
      type_eq_list{ 'tyl1; 'tyl1; small_type } } -->
   sequent [mfir] { 'H;
                    tv: ty_def{ polyKind[i:n]{'k}; tyDefPoly{t. 'ty['t]} };
                    'J['tv] >-
      type_eq{ do_tyApply{ tyDefPoly{t. 'ty['t]}; 'tyl1 };
               'ty2;
               'k } } -->
   sequent [mfir] { 'H;
                    tv: ty_def{ polyKind[i:n]{'k}; tyDefPoly{t. 'ty['t]} };
                    'J['tv] >-
      type_eq{ tyApply{ 'tv; 'tyl1 }; 'ty2; 'k } }
   = it

(*!
 * @docoff
 *)

let d_wf_tyApply1 i p =
   let j, k = Sequent.hyp_indices p i in
      wf_tyApply1 j k p

let d_wf_tyApply2 i p =
   let j, k = Sequent.hyp_indices p i in
      wf_tyApply2 j k p

let resource auto += [{
   auto_name = "d_wf_tyApply1";
   auto_prec = fir_auto_prec;
   auto_tac = onSomeHypT d_wf_tyApply1;
   auto_type = AutoNormal
}; {
   auto_name = "d_wf_tyApply2";
   auto_prec = fir_auto_prec;
   auto_tac = onSomeHypT d_wf_tyApply2;
   auto_type = AutoNormal
}]

(*!
 * @begin[doc]
 *
 * Two existential types are equal if when instantiated at the same
 * $<< small_type >>$ type, the resulting types are equal.
 * @end[doc]
 *)

prim wf_tyExists {| intro [] |} 'H 'a :
   sequent [mfir] { 'H; a: ty_def{ small_type; no_def } >-
      type_eq{ 't1['a]; 't2['a]; large_type } } -->
   sequent [mfir] { 'H >- type_eq{ tyExists{ x. 't1['x] };
                                   tyExists{ y. 't2['y] };
                                   small_type } }
   = it

(*!
 * @begin[doc]
 *
 * Two universal types are equal if when instantiated at the same
 * $<< small_type >>$ type, the resulting types are equal.
 * @end[doc]
 *)

prim wf_tyAll {| intro [] |} 'H 'a :
   sequent [mfir] { 'H; a: ty_def{ small_type; no_def } >-
      type_eq{ 't1['a]; 't2['a]; large_type } } -->
   sequent [mfir] { 'H >- type_eq{ tyAll{ x. 't1['x] };
                                   tyAll{ y. 't2['y] };
                                   small_type } }
   = it

(*!
 * @begin[doc]
 *
 * Type projections are well-formed if $i$ is in bounds.
 * @end[doc]
 *)

(*
 * BUG: We might need another rule for tyProject since we can use
 * a definition from the context to test $v.i = u$.  Or we might
 * have variable aliasing $v1 = v2 = ...$.
 *)

prim wf_tyProject 'H 'J :
   sequent [mfir] { 'H;
                    v: var_def{ polyKind[i:n]{'k}; tyExists{t. 'ty['t]} };
                    'J['v] >-
      "and"{ int_le{ 0; number[i:n] };
             int_lt{ number[i:n]; num_params{tyExists{t. 'ty['t]}} } } } -->
   sequent [mfir] { 'H;
                    v: var_def{polyKind[i:n]{'k}; tyExists{t. 'ty['t]} };
                    'J['v] >-
      type_eq{ tyProject[i:n]{ atomVar{'v} };
               tyProject[i:n]{ atomVar{'v} };
               small_type } }
   = it

(*!
 * @docoff
 *)

let d_wf_tyProject i p =
   let j, k = Sequent.hyp_indices p i in
      wf_tyProject j k p

let resource auto += {
   auto_name = "d_wf_tyProject";
   auto_prec = fir_auto_prec;
   auto_tac = onSomeHypT d_wf_tyProject;
   auto_type = AutoNormal
}

(*!
 * @begin[doc]
 * @modsubsection{Type definitions}
 *
 * Two parametrized types are equal if when instantiated at the same
 * $<< small_type >>$, the resulting types are equal.
 * @end[doc]
 *)

prim wf_tyDefPoly {| intro [] |} 'H 'a :
   sequent [mfir] { 'H; a: ty_def{ small_type; no_def } >-
      type_eq{ 'ty1['a]; 'ty2['a]; large_type } } -->
   sequent [mfir] { 'H >- type_eq{ tyDefPoly{ x. 'ty1['x] };
                                   tyDefPoly{ y. 'ty2['y] };
                                   small_type } }
   = it

(*
 * The term union_type_eq is used to test the equality of two union case
 * definitions.  It is used in the equality judgments for union definitions.
 *)

declare union_type_eq{ 'case1; 'case2 }

(*!
 * @begin[doc]
 *
 * Two union definitions are equal if the cases they define are equal, and if
 * they define the same kind of union.  Note that a union definition may
 * define zero cases.
 * @end[doc]
 *)

prim wf_tyDefUnion {| intro [] |} 'H :
   sequent [mfir] { 'H >- int_eq{ length{ 'cases1 }; number[i:n] } } -->
   sequent [mfir] { 'H >- union_type_eq{ 'cases1; 'cases2 } } -->
   sequent [mfir] { 'H >- type_eq{ tyDefUnion[str:s]{ 'cases1 };
                                   tyDefUnion[str:s]{ 'cases2 };
                                   union_type[i:n] } }
   = it

(*!
 * @begin[doc]
 *
 * Equality of union case definitions is straightforward.
 * @end[doc]
 *)

prim wf_tyDefUnion_cases1 {| intro [] |} 'H :
   sequent [mfir] { 'H >- union_type_eq{ 'h1; 'h2 } } -->
   sequent [mfir] { 'H >- union_type_eq{ 't1; 't2 } } -->
   sequent [mfir] { 'H >- union_type_eq{ cons{'h1; 't1}; cons{'h2; 't2} } }
   = it

prim wf_tyDefUnion_cases2 {| intro [] |} 'H :
   sequent [mfir] { 'H >- union_type_eq{ nil; nil } }
   = it

prim wf_tyDefUnion_unionCase {| intro [] |} 'H :
   sequent [mfir] { 'H >- union_type_eq{ 'elts1; 'elts2 } } -->
   sequent [mfir] { 'H >- union_type_eq{unionCase{'elts1}; unionCase{'elts2}}}
   = it

prim wf_tyDefUnion_unionCaseElt1 {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ 'ty1; 'ty2; large_type } } -->
   sequent [mfir] { 'H >- union_type_eq{ unionCaseElt{ 'ty1; "true" };
                                         unionCaseElt{ 'ty2; "true" } } }
   = it

prim wf_tyDefUnion_unionCaseElt2 {| intro [] |} 'H :
   sequent [mfir] { 'H >- type_eq{ 'ty1; 'ty2; large_type } } -->
   sequent [mfir] { 'H >- union_type_eq{ unionCaseElt{ 'ty1; "false" };
                                         unionCaseElt{ 'ty2; "false" } } }
   = it

(*!
 * @docoff
 *)

(**************************************************************************
 * Display forms.
 **************************************************************************)

dform union_type_eq_df : except_mode[src] ::
   union_type_eq{ 'case1; 'case2 } =
   slot{'case1} `"=" slot{'case2} `":(" bf["union case def"] `")"
