(*!
 * @begin[doc]
 * @module[Mfir_tr_atom]
 *
 * The @tt[Mfir_tr_atom] module defines the typing rules for atoms.
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

extends Mfir_int_set
extends Mfir_list
extends Mfir_ty
extends Mfir_exp
extends Mfir_sequent
extends Mfir_tr_base
extends Mfir_tr_types

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
 * @modsubsection{Normal atoms}
 *
 * The atom $<< atomInt{'i} >>$ has type $<< tyInt >>$ if $<< 'i >>$ is in the
 * set of 31-bit, signed integers.
 * @end[doc]
 *)

prim ty_atomInt {| intro [] |} 'H :
   sequent [mfir] { 'H >- member{ 'i; intset_max[31, "signed"] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ atomInt{'i}; tyInt } }
   = it

(*!
 * @begin[doc]
 *
 * An enumeration atom $<< atomEnum[i:n]{'n} >>$ has type $<< tyEnum[i:n] >>$
 * if $ 0 <<le>> n < i $, and if $<< tyEnum[i:n] >>$ is a well-formed type
 * (that is, if $<< member{ number[i:n]; enum_max } >>$).
 * @end[doc]
 *)

prim ty_atomEnum {| intro [] |} 'H :
   sequent [mfir] { 'H >- member{ number[i:n]; enum_max } } -->
   sequent [mfir] { 'H >- "and"{int_le{0; 'n}; int_lt{'n; number[i:n]}} } -->
   sequent [mfir] { 'H >- has_type["atom"]{atomEnum[i:n]{'n}; tyEnum[i:n]} }
   = it

(*!
 * @begin[doc]
 *
 * The atom $<< atomRawInt[p:n, sign:s]{'i} >>$ has type
 * $<< tyRawInt[p:n, sign:s] >>$, if $i$ is in the appropriate set of
 * integers, and if $<< tyRawInt[p:n, sign:s] >>$ is a well-formed type.
 * @end[doc]
 *)

prim ty_atomRawInt 'H :
   sequent [mfir] { 'H >- type_eq{ tyRawInt[p:n, sign:s];
                                   tyRawInt[p:n, sign:s];
                                   polyKind[0]{large_type} } } -->
   sequent [mfir] { 'H >- member{ 'i; intset_max[p:n, sign:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomRawInt[p:n, sign:s]{'i}; tyRawInt[p:n, sign:s] } }
   = it

(*!
 * @begin[doc]
 *
 * A variable $<< atomVar{'v} >>$ has type $<< 'ty >>$ if it is declared in
 * the context to have type $<< 'ty >>$.
 * @end[doc]
 *)

prim ty_atomVar 'H 'J :
   sequent [mfir] { 'H; v: var_def{ 'ty; 'd }; 'J['v] >-
      has_type["atom"]{ atomVar{'v}; 'ty } }
   = it

(*!
 * @docoff
 *)

let d_ty_atomVar i p =
   let j, k = Sequent.hyp_indices p i in
      ty_atomVar j k p

let resource auto += {
   auto_name = "d_ty_atomVar";
   auto_prec = fir_auto_prec;
   auto_tac = onSomeHypT d_ty_atomVar;
   auto_type = AutoNormal
}

(*!
 * @begin[doc]
 * @modsubsection{Polymorphism}
 *
 * The atom $<< atomTyApply{ atomVar{'v}; 'u1; 'types } >>$ instantiates
 * $<< atomVar{'v} >>$ at a list of types, where $<< atomVar{'v} >>$ should
 * have a universal type.
 * @end[doc]
 *)

prim ty_atomTyApply 'H 'J :
   (* The type of the atom must agree with what it thinks its own type is. *)
   sequent [mfir] { 'H;
                    v: var_def{ tyAll{ t. 'ty['t] }; 'd };
                    'J['v] >-
      type_eq{ 'u1; 'u2; polyKind[0]{ small_type } } } -->

   (* The types being applied should be small. *)
   sequent [mfir] { 'H;
                    v: var_def{ tyAll{ t. 'ty['t] }; 'd };
                    'J['v] >-
      type_eq_list{ 'types; 'types; polyKind[0]{ small_type } } } -->

   (* The type should correspond to the tyAll applied to the given types. *)
   sequent [mfir] { 'H;
                    v: var_def{ tyAll{ t. 'ty['t] }; 'd };
                    'J['v] >-
      type_eq{ 'u1;
               do_tyApply{ tyAll{ t. 'ty['t] }; 'types };
               polyKind[0]{ small_type } } } -->

   (* Then the atom is well-typed. *)
   sequent [mfir] { 'H;
                    v: var_def{ tyAll{ t. 'ty['t] }; 'd };
                    'J['v] >-
      has_type["atom"]{ atomTyApply{ atomVar{'v}; 'u1; 'types };
                        'u2 } }
   = it

(*!
 * @docoff
 *)

let d_ty_atomTyApply i p =
   let j, k = Sequent.hyp_indices p i in
      ty_atomTyApply j k p

let resource auto += {
   auto_name = "d_ty_atomTyApply";
   auto_prec = fir_auto_prec;
   auto_tac = onSomeHypT d_ty_atomTyApply;
   auto_type = AutoNormal
}

(*!
 * @begin[doc]
 *
 * The atom $<< atomTyPack{ 'var; 'u; 'types } >>$ is the introduction
 * form for type packing.  A value is packaged with a list of types
 * to form a value with an existential type.
 * @end[doc]
 *)

prim ty_atomTyPack {| intro [] |} 'H :
   sequent [mfir] { 'H >-
      type_eq_list{ 'types; 'types; polyKind[0]{ small_type } } } -->
   sequent [mfir] { 'H >-
      type_eq{ 'u; tyExists{ t. 'ty['t] }; polyKind[0]{ small_type } } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ 'var; do_tyApply{tyExists{t. 'ty['t]}; 'types} } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomTyPack{ 'var; 'u; 'types };
                        tyExists{ t. 'ty['t] } } }
   = it

(*!
 * @begin[doc]
 *
 * The atom $<< atomTyUnpack{ atomVar{'v} } >>$ is the elimination
 * form for type packing.  If $<< atomVar{'v} >>$ has an existential type
 * $t$, then the type unpacking has a type equal to $t$ instantiated
 * at the types from the original packing.
 * @end[doc]
 *)

prim ty_atomTyUnpack 'H 'J:
   sequent [mfir] { 'H;
                    v: var_def{ tyExists{ t. 'ty['t] }; 'd };
                    'J['v] >-
      type_eq{ 'u;
               instantiate_tyExists{ tyExists{ t. 'ty['t] }; 'v; 0 };
               polyKind[0]{ large_type } } } -->
   sequent [mfir] { 'H;
                    v: var_def{ tyExists{ t. 'ty['t] }; 'd };
                    'J['v] >-
      has_type["atom"]{ atomTyUnpack{ atomVar{'v} }; 'u } }
   = it

(*!
 * @docoff
 *)

let d_ty_atomTyUnpack i p =
   let j, k = Sequent.hyp_indices p i in
      ty_atomTyUnpack j k p

let resource auto += {
   auto_name = "d_ty_atomTyUnpack";
   auto_prec = fir_auto_prec;
   auto_tac = onSomeHypT d_ty_atomTyUnpack;
   auto_type = AutoNormal
}

(*!
 * @begin[doc]
 * @modsubsection{Unary and binary operators}
 *
 * For the atoms $<< atomUnop{ 'unop; 'a } >>$ and
 * $<< atomBinop{ 'binop; 'a1; 'a2 } >>$, there is a typing rule for each
 * possible operator.  The rules are straightforward, and we will illustrate
 * their basic form with two examples.
 * @end[doc]
 *)

prim ty_uminusIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a ; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{atomUnop{uminusIntOp; 'a}; tyInt} }
   = it

prim ty_plusIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{plusIntOp; 'a1; 'a2}; tyInt } }
   = it

(*!
 * @docoff
 *)

(*
 * Unary operators.
 *)

prim ty_idOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a; 'ty } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ atomUnop{ idOp; 'a }; 'ty } }
   = it

(* uminusIntOp is one of the examples above. *)

prim ty_notIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ atomUnop{ notIntOp; 'a}; tyInt } }
   = it

(* NOTE: Using the Mojave compiler rule for rawBitFieldOp. *)

prim ty_rawBitFieldOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- member{ 'i1; intset_max[p:n, s:s] } } -->
   sequent [mfir] { 'H >- member{ 'i2; intset_max[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomUnop{ rawBitFieldOp[p:n, s:s]{ 'i1; 'i2 }; 'a };
                        tyRawInt[p:n, s:s] } }
   = it

prim ty_uminusRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomUnop{ uminusRawIntOp[p:n, s:s]; 'a };
                        tyRawInt[p:n, s:s] } }
   = it

prim ty_notRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomUnop{ notRawIntOp[p:n, s:s]; 'a };
                        tyRawInt[p:n, s:s] } }
   = it

prim ty_uminusFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomUnop{ uminusFloatOp[p:n]; 'a };
                        tyFloat[p:n] } }
   = it

prim ty_absFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomUnop{ absFloatOp[p:n]; 'a };
                        tyFloat[p:n] } }
   = it

prim ty_sinOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomUnop{ sinOp[p:n]; 'a };
                        tyFloat[p:n] } }
   = it

prim ty_cosOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomUnop{ cosOp[p:n]; 'a };
                        tyFloat[p:n] } }
   = it

prim ty_sqrtOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomUnop{ sqrtOp[p:n]; 'a };
                        tyFloat[p:n] } }
   = it

prim ty_intOfFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomUnop{ intOfFloatOp[p:n]; 'a }; tyInt } }
   = it

prim ty_floatOfIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomUnop{ floatOfIntOp[p:n]; 'a };
                        tyFloat[p:n] } }
   = it

prim ty_floatOfFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a; tyFloat[src:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomUnop{ floatOfFloatOp[dest:n, src:n]; 'a };
                        tyFloat[dest:n] } }
   = it

prim ty_floatOfRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a; tyRawInt[ip:n, is:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomUnop{ floatOfRawIntOp[fp:n, ip:n, is:s]; 'a };
                        tyFloat[fp:n] } }
   = it

prim ty_rawIntOfIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomUnop{ rawIntOfIntOp[p:n, s:s]; 'a };
                        tyRawInt[p:n, s:s] } }
   = it

prim ty_rawIntOfEnumOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a; tyEnum[i:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomUnop{ rawIntOfEnumOp[p:n, s:s, i:n]; 'a };
                        tyRawInt[p:n, s:s] } }
   = it

prim ty_rawIntOfFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a; tyFloat[fp:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomUnop{ rawIntOfFloatOp[ip:n, s:s, fp:n]; 'a };
                        tyRawInt[ip:n, s:s] } }
   = it

prim ty_rawIntOfRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a; tyRawInt[sp:n, ss:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{atomUnop{rawIntOfRawIntOp[dp:n, ds:s, sp:n, ss:s]; 'a};
                       tyRawInt[dp:n, ds:s]} }
   = it

(*
 * Binary operators.
 *)

prim ty_andEnumOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyEnum[i:n] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyEnum[i:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ andEnumOp[i:n]; 'a1; 'a2 }; tyEnum[i:n] } }
   = it

prim ty_orEnumOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyEnum[i:n] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyEnum[i:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ orEnumOp[i:n]; 'a1; 'a2 }; tyEnum[i:n] } }
   = it

prim ty_xorEnumOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyEnum[i:n] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyEnum[i:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ xorEnumOp[i:n]; 'a1; 'a2 }; tyEnum[i:n] } }
   = it

(* plusIntOP is an example above. *)

prim ty_minusIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ minusIntOp; 'a1; 'a2 }; tyInt } }
   = it

prim ty_mulIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ mulIntOp; 'a1; 'a2 }; tyInt } }
   = it

prim ty_divIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ divIntOp; 'a1; 'a2 }; tyInt } }
   = it

prim ty_remIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ remIntOp; 'a1; 'a2 }; tyInt } }
   = it

prim ty_lslIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ lslIntOp; 'a1; 'a2 }; tyInt } }
   = it

prim ty_lsrIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ lsrIntOp; 'a1; 'a2 }; tyInt } }
   = it

prim ty_asrIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ asrIntOp; 'a1; 'a2 }; tyInt } }
   = it

prim ty_andIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ andIntOp; 'a1; 'a2 }; tyInt } }
   = it

prim ty_orIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ orIntOp; 'a1; 'a2 }; tyInt } }
   = it

prim ty_xorIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ xorIntOp; 'a1; 'a2 }; tyInt } }
   = it

prim ty_maxIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ maxIntOp; 'a1; 'a2 }; tyInt } }
   = it

prim ty_minIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ minIntOp; 'a1; 'a2 }; tyInt } }
   = it

prim ty_eqIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ eqIntOp; 'a1; 'a2 }; tyEnum[2] } }
   = it

prim ty_neqIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ neqIntOp; 'a1; 'a2 }; tyEnum[2] } }
   = it

prim ty_ltIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ ltIntOp; 'a1; 'a2 }; tyEnum[2] } }
   = it

prim ty_leIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ leIntOp; 'a1; 'a2 }; tyEnum[2] } }
   = it

prim ty_gtIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ gtIntOp; 'a1; 'a2 }; tyEnum[2] } }
   = it

prim ty_geIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ geIntOp; 'a1; 'a2 }; tyEnum[2] } }
   = it

prim ty_cmpIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyInt } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyInt } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ cmpIntOp; 'a1; 'a2 }; tyInt } }
   = it

prim ty_plusRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ plusRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyRawInt[p:n, s:s] } }
   = it

prim ty_minusRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ minusRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyRawInt[p:n, s:s] } }
   = it

prim ty_mulRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ mulRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyRawInt[p:n, s:s] } }
   = it

prim ty_divRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ divRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyRawInt[p:n, s:s] } }
   = it

prim ty_remRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ remRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyRawInt[p:n, s:s] } }
   = it

prim ty_slRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ slRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyRawInt[p:n, s:s] } }
   = it

prim ty_srRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ srRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyRawInt[p:n, s:s] } }
   = it

prim ty_andRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ andRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyRawInt[p:n, s:s] } }
   = it

prim ty_orRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ orRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyRawInt[p:n, s:s] } }
   = it

prim ty_xorRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ xorRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyRawInt[p:n, s:s] } }
   = it

prim ty_maxRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ maxRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyRawInt[p:n, s:s] } }
   = it

prim ty_minRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ minRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyRawInt[p:n, s:s] } }
   = it

(* NOTE: Using the Mojave compiler rule for rawSetBitFieldOp. *)

prim ty_rawSetBitFieldOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- member{ 'i1; intset_max[p:n, s:s] } } -->
   sequent [mfir] { 'H >- member{ 'i2; intset_max[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ rawSetBitFieldOp[p:n, s:s]{'i1; 'i2};
                                   'a1; 'a2};
                        tyRawInt[p:n, s:s] } }
   = it

prim ty_eqRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ eqRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyEnum[2] } }
   = it

prim ty_neqRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ neqRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyEnum[2] } }
   = it

prim ty_ltRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ ltRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyEnum[2] } }
   = it

prim ty_leRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ leRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyEnum[2] } }
   = it

prim ty_gtRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ gtRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyEnum[2] } }
   = it

prim ty_geRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ geRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyEnum[2] } }
   = it

prim ty_cmpRawIntOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyRawInt[p:n, s:s] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ cmpRawIntOp[p:n, s:s]; 'a1; 'a2 };
                        tyInt } }
   = it

prim ty_plusFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ plusFloatOp[p:n]; 'a1; 'a2 };
                        tyFloat[p:n] } }
   = it

prim ty_minusFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ minusFloatOp[p:n]; 'a1; 'a2 };
                        tyFloat[p:n] } }
   = it

prim ty_mulFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ mulFloatOp[p:n]; 'a1; 'a2 };
                        tyFloat[p:n] } }
   = it

prim ty_divFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ divFloatOp[p:n]; 'a1; 'a2 };
                        tyFloat[p:n] } }
   = it

prim ty_remFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ remFloatOp[p:n]; 'a1; 'a2 };
                        tyFloat[p:n] } }
   = it

prim ty_maxFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ maxFloatOp[p:n]; 'a1; 'a2 };
                        tyFloat[p:n] } }
   = it

prim ty_minFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ minFloatOp[p:n]; 'a1; 'a2 };
                        tyFloat[p:n] } }
   = it

prim ty_eqFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ eqFloatOp[p:n]; 'a1; 'a2 }; tyEnum[2] } }
   = it

prim ty_neqFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ neqFloatOp[p:n]; 'a1; 'a2 }; tyEnum[2] } }
   = it

prim ty_ltFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ ltFloatOp[p:n]; 'a1; 'a2 }; tyEnum[2] } }
   = it


prim ty_leFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ leFloatOp[p:n]; 'a1; 'a2 }; tyEnum[2] } }
   = it

prim ty_gtFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ gtFloatOp[p:n]; 'a1; 'a2 }; tyEnum[2] } }
   = it

prim ty_geFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ geFloatOp[p:n]; 'a1; 'a2 }; tyEnum[2] } }
   = it

prim ty_cmpFloatOp {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ cmpFloatOp[p:n]; 'a1; 'a2 }; tyInt } }
   = it

prim ty_atan2Op {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; tyFloat[p:n] } } -->
   sequent [mfir] { 'H >-
      has_type["atom"]{ atomBinop{ atan2Op[p:n]; 'a1; 'a2 }; tyFloat[p:n] } }
   = it
