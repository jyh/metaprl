(*!
 * @begin[doc]
 * @module[Mfir_tr_atom_base]
 *
 * The @tt[Mfir_tr_atom_base] module defines the argument types
 * and result types of the FIR operators.
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

extends Mfir_ty
extends Mfir_exp
extends Mfir_sequent


(**************************************************************************
 * Declarations.
 **************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The term @tt[res_type] returns the result type of an operator @tt[op].
 * The terms @tt[arg1_type] and @tt[arg2_type] return the types of
 * first and second arguments of an operator @tt[op] (@tt[arg2_type] is
 * undefined if @tt[op] is a unary operator).
 * @end[doc]
 *)

declare res_type{ 'op }
declare arg1_type{ 'op }
declare arg2_type{ 'op }

(*!
 * @docoff
 *)


(**************************************************************************
 * Display forms.
 **************************************************************************)

dform res_type_df : except_mode[src] ::
   res_type{ 'op } =
   bf["res_type"] `"(" slot{'op} `")"

dform arg1_type_df : except_mode[src] ::
   arg1_type{ 'op } =
   bf["arg1_type"] `"(" slot{'op} `")"

dform arg2_type_df : except_mode[src] ::
   arg2_type{ 'op } =
   bf["arg2_type"] `"(" slot{'op} `")"


(**************************************************************************
 * Rewrites.
 **************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * Rewrites are used to define the argument and result types of the
 * FIR unary and binary operators.  The types may not be well-formed
 * if the original operator is not well-formed.  We omit an explicit
 * listing of these rewrites.
 * @end[doc]
 *)

(*!
 * @docoff
 *)

prim_rw reduce_res_type_notEnumOp :
   res_type{ notEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_arg1_type_notEnumOp :
   arg1_type{ notEnumOp[i:n] } <-->
   tyEnum[i:n]

let resource reduce += [
   << res_type{ notEnumOp[i:n] } >>, reduce_res_type_notEnumOp;
   << arg1_type{ notEnumOp[i:n] } >>, reduce_arg1_type_notEnumOp;
]


prim_rw reduce_res_type_uminusIntOp :
   res_type{ uminusIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_uminusIntOp :
   arg1_type{ uminusIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ uminusIntOp } >>, reduce_res_type_uminusIntOp;
   << arg1_type{ uminusIntOp } >>, reduce_arg1_type_uminusIntOp;
]


prim_rw reduce_res_type_notIntOp :
   res_type{ notIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_notIntOp :
   arg1_type{ notIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ notIntOp } >>, reduce_res_type_notIntOp;
   << arg1_type{ notIntOp } >>, reduce_arg1_type_notIntOp;
]


prim_rw reduce_res_type_absIntOp :
   res_type{ absIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_absIntOp :
   arg1_type{ absIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ absIntOp } >>, reduce_res_type_absIntOp;
   << arg1_type{ absIntOp } >>, reduce_arg1_type_absIntOp;
]


prim_rw reduce_res_type_uminusRawIntOp :
   res_type{ uminusRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_uminusRawIntOp :
   arg1_type{ uminusRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ uminusRawIntOp[p:n, s:s] } >>, reduce_res_type_uminusRawIntOp;
   << arg1_type{ uminusRawIntOp[p:n, s:s] } >>, reduce_arg1_type_uminusRawIntOp;
]


prim_rw reduce_res_type_notRawIntOp :
   res_type{ notRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_notRawIntOp :
   arg1_type{ notRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ notRawIntOp[p:n, s:s] } >>, reduce_res_type_notRawIntOp;
   << arg1_type{ notRawIntOp[p:n, s:s] } >>, reduce_arg1_type_notRawIntOp;
]


prim_rw reduce_res_type_uminusFloatOp :
   res_type{ uminusFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_uminusFloatOp :
   arg1_type{ uminusFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ uminusFloatOp[p:n] } >>, reduce_res_type_uminusFloatOp;
   << arg1_type{ uminusFloatOp[p:n] } >>, reduce_arg1_type_uminusFloatOp;
]


prim_rw reduce_res_type_absFloatOp :
   res_type{ absFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_absFloatOp :
   arg1_type{ absFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ absFloatOp[p:n] } >>, reduce_res_type_absFloatOp;
   << arg1_type{ absFloatOp[p:n] } >>, reduce_arg1_type_absFloatOp;
]


prim_rw reduce_res_type_sinFloatOp :
   res_type{ sinFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_sinFloatOp :
   arg1_type{ sinFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ sinFloatOp[p:n] } >>, reduce_res_type_sinFloatOp;
   << arg1_type{ sinFloatOp[p:n] } >>, reduce_arg1_type_sinFloatOp;
]


prim_rw reduce_res_type_cosFloatOp :
   res_type{ cosFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_cosFloatOp :
   arg1_type{ cosFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ cosFloatOp[p:n] } >>, reduce_res_type_cosFloatOp;
   << arg1_type{ cosFloatOp[p:n] } >>, reduce_arg1_type_cosFloatOp;
]


prim_rw reduce_res_type_tanFloatop :
   res_type{ tanFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_tanFloatop :
   arg1_type{ tanFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ tanFloatOp[p:n] } >>, reduce_res_type_tanFloatop;
   << arg1_type{ tanFloatOp[p:n] } >>, reduce_arg1_type_tanFloatop;
]


prim_rw reduce_res_type_asinFloatOp :
   res_type{ asinFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_asinFloatOp :
   arg1_type{ asinFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ asinFloatOp[p:n] } >>, reduce_res_type_asinFloatOp;
   << arg1_type{ asinFloatOp[p:n] } >>, reduce_arg1_type_asinFloatOp;
]


prim_rw reduce_res_type_atanFloatOp :
   res_type{ atanFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_atanFloatOp :
   arg1_type{ atanFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ atanFloatOp[p:n] } >>, reduce_res_type_atanFloatOp;
   << arg1_type{ atanFloatOp[p:n] } >>, reduce_arg1_type_atanFloatOp;
]


prim_rw reduce_res_type_sinhFloatOp :
   res_type{ sinhFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_sinhFloatOp :
   arg1_type{ sinhFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ sinhFloatOp[p:n] } >>, reduce_res_type_sinhFloatOp;
   << arg1_type{ sinhFloatOp[p:n] } >>, reduce_arg1_type_sinhFloatOp;
]


prim_rw reduce_res_type_coshFloatOp :
   res_type{ coshFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_coshFloatOp :
   arg1_type{ coshFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ coshFloatOp[p:n] } >>, reduce_res_type_coshFloatOp;
   << arg1_type{ coshFloatOp[p:n] } >>, reduce_arg1_type_coshFloatOp;
]


prim_rw reduce_res_type_tanhFloatOp :
   res_type{ tanhFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_tanhFloatOp :
   arg1_type{ tanhFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ tanhFloatOp[p:n] } >>, reduce_res_type_tanhFloatOp;
   << arg1_type{ tanhFloatOp[p:n] } >>, reduce_arg1_type_tanhFloatOp;
]


prim_rw reduce_res_type_expFloatOp :
   res_type{ expFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_expFloatOp :
   arg1_type{ expFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ expFloatOp[p:n] } >>, reduce_res_type_expFloatOp;
   << arg1_type{ expFloatOp[p:n] } >>, reduce_arg1_type_expFloatOp;
]


prim_rw reduce_res_type_logFloatOp :
   res_type{ logFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_logFloatOp :
   arg1_type{ logFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ logFloatOp[p:n] } >>, reduce_res_type_logFloatOp;
   << arg1_type{ logFloatOp[p:n] } >>, reduce_arg1_type_logFloatOp;
]


prim_rw reduce_res_type_sqrtFloatOp :
   res_type{ sqrtFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_sqrtFloatOp :
   arg1_type{ sqrtFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ sqrtFloatOp[p:n] } >>, reduce_res_type_sqrtFloatOp;
   << arg1_type{ sqrtFloatOp[p:n] } >>, reduce_arg1_type_sqrtFloatOp;
]


prim_rw reduce_res_type_ceilFloatOp :
   res_type{ ceilFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_ceilFloatOp :
   arg1_type{ ceilFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ ceilFloatOp[p:n] } >>, reduce_res_type_ceilFloatOp;
   << arg1_type{ ceilFloatOp[p:n] } >>, reduce_arg1_type_ceilFloatOp;
]


prim_rw reduce_res_type_floorFloatOp :
   res_type{ floorFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_floorFloatOp :
   arg1_type{ floorFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ floorFloatOp[p:n] } >>, reduce_res_type_floorFloatOp;
   << arg1_type{ floorFloatOp[p:n] } >>, reduce_arg1_type_floorFloatOp;
]


prim_rw reduce_res_type_intOfFloatOp :
   res_type{ intOfFloatOp[p:n] } <-->
   tyInt

prim_rw reduce_arg1_type_intOfFloatOp :
   arg1_type{ intOfFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ intOfFloatOp[p:n] } >>, reduce_res_type_intOfFloatOp;
   << arg1_type{ intOfFloatOp[p:n] } >>, reduce_arg1_type_intOfFloatOp;
]


prim_rw reduce_res_type_intOfRawIntOp :
   res_type{ intOfRawIntOp[p:n, s:s] } <-->
   tyInt

prim_rw reduce_arg1_type_intOfRawIntOp :
   arg1_type{ intOfRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ intOfRawIntOp[p:n, s:s] } >>, reduce_res_type_intOfRawIntOp;
   << arg1_type{ intOfRawIntOp[p:n, s:s] } >>, reduce_arg1_type_intOfRawIntOp;
]


prim_rw reduce_res_type_floatOfIntOp :
   res_type{ floatOfIntOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_floatOfIntOp :
   arg1_type{ floatOfIntOp[p:n] } <-->
   tyInt

let resource reduce += [
   << res_type{ floatOfIntOp[p:n] } >>, reduce_res_type_floatOfIntOp;
   << arg1_type{ floatOfIntOp[p:n] } >>, reduce_arg1_type_floatOfIntOp;
]


prim_rw reduce_res_type_floatOfFloatOp :
   res_type{ floatOfFloatOp[p1:n, p2:n] } <-->
   tyFloat[p1:n]

prim_rw reduce_arg1_type_floatOfFloatOp :
   arg1_type{ floatOfFloatOp[p1:n, p2:n] } <-->
   tyFloat[p2:n]

let resource reduce += [
   << res_type{ floatOfFloatOp[p1:n, p2:n] } >>, reduce_res_type_floatOfFloatOp;
   << arg1_type{ floatOfFloatOp[p1:n, p2:n] } >>, reduce_arg1_type_floatOfFloatOp;
]


prim_rw reduce_res_type_floatOfRawIntOp :
   res_type{ floatOfRawIntOp[fp:n, rp:n, s:s] } <-->
   tyFloat[fp:n]

prim_rw reduce_arg1_type_floatOfRawIntOp :
   arg1_type{ floatOfRawIntOp[fp:n, rp:n, s:s] } <-->
   tyRawInt[rp:n, s:s]

let resource reduce += [
   << res_type{ floatOfRawIntOp[fp:n, rp:n, s:s] } >>, reduce_res_type_floatOfRawIntOp;
   << arg1_type{ floatOfRawIntOp[fp:n, rp:n, s:s] } >>, reduce_arg1_type_floatOfRawIntOp;
]


prim_rw reduce_res_type_rawIntOfIntOp :
   res_type{ rawIntOfIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_rawIntOfIntOp :
   arg1_type{ rawIntOfIntOp[p:n, s:s] } <-->
   tyInt

let resource reduce += [
   << res_type{ rawIntOfIntOp[p:n, s:s] } >>, reduce_res_type_rawIntOfIntOp;
   << arg1_type{ rawIntOfIntOp[p:n, s:s] } >>, reduce_arg1_type_rawIntOfIntOp;
]


prim_rw reduce_res_type_rawIntOfEnumOp :
   res_type{ rawIntOfEnumOp[p:n, s:s, i:n] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_rawIntOfEnumOp :
   arg1_type{ rawIntOfEnumOp[p:n, s:s, i:n] } <-->
   tyEnum[i:n]

let resource reduce += [
   << res_type{ rawIntOfEnumOp[p:n, s:s, i:n] } >>, reduce_res_type_rawIntOfEnumOp;
   << arg1_type{ rawIntOfEnumOp[p:n, s:s, i:n] } >>, reduce_arg1_type_rawIntOfEnumOp;
]


prim_rw reduce_res_type_rawIntOfFloatOp :
   res_type{ rawIntOfFloatOp[rp:n, s:s, fp:n] } <-->
   tyRawInt[rp:n, s:s]

prim_rw reduce_arg1_type_rawIntOfFloatOp :
   arg1_type{ rawIntOfFloatOp[rp:n, s:s, fp:n] } <-->
   tyFloat[fp:n]

let resource reduce += [
   << res_type{ rawIntOfFloatOp[rp:n, s:s, fp:n] } >>, reduce_res_type_rawIntOfFloatOp;
   << arg1_type{ rawIntOfFloatOp[rp:n, s:s, fp:n] } >>, reduce_arg1_type_rawIntOfFloatOp;
]


prim_rw reduce_res_type_rawIntOfRawIntOp :
   res_type{ rawIntOfRawIntOp[dp:n, ds:s, sp:n, ss:s] } <-->
   tyRawInt[dp:n, ds:s]

prim_rw reduce_arg1_type_rawIntOfRawIntOp :
   arg1_type{ rawIntOfRawIntOp[dp:n, ds:s, sp:n, ss:s] } <-->
   tyRawInt[sp:n, ss:s]

let resource reduce += [
   << res_type{ rawIntOfRawIntOp[dp:n, ds:s, sp:n, ss:s] } >>, reduce_res_type_rawIntOfRawIntOp;
   << arg1_type{ rawIntOfRawIntOp[dp:n, ds:s, sp:n, ss:s] } >>, reduce_arg1_type_rawIntOfRawIntOp;
]


prim_rw reduce_res_type_dtupleOfDTupleOp :
   res_type{ dtupleOfDTupleOp{ 'tv; 'mtyl } } <-->
   tyDTuple{ 'tv; none }

prim_rw reduce_arg1_type_dtupleOfDTupleOp :
   arg1_type{ dtupleOfDTupleOp{ 'tv; 'mtyl } } <-->
   tyDTuple{ 'tv; some{ 'mtyl } }

let resource reduce += [
   << res_type{ dtupleOfDTupleOp{ 'tv; 'mtyl } } >>, reduce_res_type_dtupleOfDTupleOp;
   << arg1_type{ dtupleOfDTupleOp{ 'tv; 'mtyl } } >>, reduce_arg1_type_dtupleOfDTupleOp;
]


prim_rw reduce_res_type_unionOfUnionOp :
   res_type{ unionOfUnionOp{ 'tv; 'tyl; 's1; 's2 } } <-->
   tyUnion{ 'tv; 'tyl; 's1 }

prim_rw reduce_arg1_type_unionOfUnionOp :
   arg1_type{ unionOfUnionOp{ 'tv; 'tyl; 's1; 's2 } } <-->
   tyUnion{ 'tv; 'tyl; 's2 }

let resource reduce += [
   << res_type{ unionOfUnionOp{ 'tv; 'tyl; 's1; 's2 } } >>, reduce_res_type_unionOfUnionOp;
   << arg1_type{ unionOfUnionOp{ 'tv; 'tyl; 's1; 's2 } } >>, reduce_arg1_type_unionOfUnionOp;
]


prim_rw reduce_res_type_rawDataOfFrameOp :
   res_type{ rawDataOfFrameOp{ 'tv; 'tyl } } <-->
   tyRawData

prim_rw reduce_arg1_type_rawDataOfFrameOp :
   arg1_type{ rawDataOfFrameOp{ 'tv; 'tyl } } <-->
   tyFrame{ 'tv; 'tyl }

let resource reduce += [
   << res_type{ rawDataOfFrameOp{ 'tv; 'tyl } } >>, reduce_res_type_rawDataOfFrameOp;
   << arg1_type{ rawDataOfFrameOp{ 'tv; 'tyl } } >>, reduce_arg1_type_rawDataOfFrameOp;
]


prim_rw reduce_res_type_andEnumOp :
   res_type{ andEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_arg1_type_andEnumOp :
   arg1_type{ andEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_arg2_type_andEnumOp :
   arg2_type { andEnumOp[i:n] } <-->
   tyEnum[i:n]

let resource reduce += [
   << res_type{ andEnumOp[i:n] } >>, reduce_res_type_andEnumOp;
   << arg1_type{ andEnumOp[i:n] } >>, reduce_arg1_type_andEnumOp;
   << arg2_type{ andEnumOp[i:n] } >>, reduce_arg2_type_andEnumOp;
]


prim_rw reduce_res_type_orEnumOp :
   res_type{ orEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_arg1_type_orEnumOp :
   arg1_type{ orEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_arg2_type_orEnumOp :
   arg2_type { orEnumOp[i:n] } <-->
   tyEnum[i:n]

let resource reduce += [
   << res_type{ orEnumOp[i:n] } >>, reduce_res_type_orEnumOp;
   << arg1_type{ orEnumOp[i:n] } >>, reduce_arg1_type_orEnumOp;
   << arg2_type{ orEnumOp[i:n] } >>, reduce_arg2_type_orEnumOp;
]


prim_rw reduce_res_type_xorEnumOp :
   res_type{ xorEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_arg1_type_xorEnumOp :
   arg1_type{ xorEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_arg2_type_xorEnumOp :
   arg2_type { xorEnumOp[i:n] } <-->
   tyEnum[i:n]

let resource reduce += [
   << res_type{ xorEnumOp[i:n] } >>, reduce_res_type_xorEnumOp;
   << arg1_type{ xorEnumOp[i:n] } >>, reduce_arg1_type_xorEnumOp;
   << arg2_type{ xorEnumOp[i:n] } >>, reduce_arg2_type_xorEnumOp;
]


prim_rw reduce_res_type_plusIntOp :
   res_type{ plusIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_plusIntOp :
   arg1_type{ plusIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_plusIntOp :
   arg2_type { plusIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ plusIntOp } >>, reduce_res_type_plusIntOp;
   << arg1_type{ plusIntOp } >>, reduce_arg1_type_plusIntOp;
   << arg2_type{ plusIntOp } >>, reduce_arg2_type_plusIntOp;
]


prim_rw reduce_res_type_minusIntOp :
   res_type{ minusIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_minusIntOp :
   arg1_type{ minusIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_minusIntOp :
   arg2_type { minusIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ minusIntOp } >>, reduce_res_type_minusIntOp;
   << arg1_type{ minusIntOp } >>, reduce_arg1_type_minusIntOp;
   << arg2_type{ minusIntOp } >>, reduce_arg2_type_minusIntOp;
]


prim_rw reduce_res_type_mulIntOp :
   res_type{ mulIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_mulIntOp :
   arg1_type{ mulIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_mulIntOp :
   arg2_type { mulIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ mulIntOp } >>, reduce_res_type_mulIntOp;
   << arg1_type{ mulIntOp } >>, reduce_arg1_type_mulIntOp;
   << arg2_type{ mulIntOp } >>, reduce_arg2_type_mulIntOp;
]


prim_rw reduce_res_type_divIntOp :
   res_type{ divIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_divIntOp :
   arg1_type{ divIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_divIntOp :
   arg2_type { divIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ divIntOp } >>, reduce_res_type_divIntOp;
   << arg1_type{ divIntOp } >>, reduce_arg1_type_divIntOp;
   << arg2_type{ divIntOp } >>, reduce_arg2_type_divIntOp;
]


prim_rw reduce_res_type_remIntOp :
   res_type{ remIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_remIntOp :
   arg1_type{ remIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_remIntOp :
   arg2_type { remIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ remIntOp } >>, reduce_res_type_remIntOp;
   << arg1_type{ remIntOp } >>, reduce_arg1_type_remIntOp;
   << arg2_type{ remIntOp } >>, reduce_arg2_type_remIntOp;
]


prim_rw reduce_res_type_lslIntOp :
   res_type{ lslIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_lslIntOp :
   arg1_type{ lslIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_lslIntOp :
   arg2_type { lslIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ lslIntOp } >>, reduce_res_type_lslIntOp;
   << arg1_type{ lslIntOp } >>, reduce_arg1_type_lslIntOp;
   << arg2_type{ lslIntOp } >>, reduce_arg2_type_lslIntOp;
]


prim_rw reduce_res_type_lsrIntOp :
   res_type{ lsrIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_lsrIntOp :
   arg1_type{ lsrIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_lsrIntOp :
   arg2_type { lsrIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ lsrIntOp } >>, reduce_res_type_lsrIntOp;
   << arg1_type{ lsrIntOp } >>, reduce_arg1_type_lsrIntOp;
   << arg2_type{ lsrIntOp } >>, reduce_arg2_type_lsrIntOp;
]


prim_rw reduce_res_type_asrIntOp :
   res_type{ asrIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_asrIntOp :
   arg1_type{ asrIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_asrIntOp :
   arg2_type { asrIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ asrIntOp } >>, reduce_res_type_asrIntOp;
   << arg1_type{ asrIntOp } >>, reduce_arg1_type_asrIntOp;
   << arg2_type{ asrIntOp } >>, reduce_arg2_type_asrIntOp;
]


prim_rw reduce_res_type_andIntOp :
   res_type{ andIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_andIntOp :
   arg1_type{ andIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_andIntOp :
   arg2_type { andIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ andIntOp } >>, reduce_res_type_andIntOp;
   << arg1_type{ andIntOp } >>, reduce_arg1_type_andIntOp;
   << arg2_type{ andIntOp } >>, reduce_arg2_type_andIntOp;
]


prim_rw reduce_res_type_orIntOp :
   res_type{ orIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_orIntOp :
   arg1_type{ orIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_orIntOp :
   arg2_type { orIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ orIntOp } >>, reduce_res_type_orIntOp;
   << arg1_type{ orIntOp } >>, reduce_arg1_type_orIntOp;
   << arg2_type{ orIntOp } >>, reduce_arg2_type_orIntOp;
]


prim_rw reduce_res_type_xorIntOp :
   res_type{ xorIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_xorIntOp :
   arg1_type{ xorIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_xorIntOp :
   arg2_type { xorIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ xorIntOp } >>, reduce_res_type_xorIntOp;
   << arg1_type{ xorIntOp } >>, reduce_arg1_type_xorIntOp;
   << arg2_type{ xorIntOp } >>, reduce_arg2_type_xorIntOp;
]


prim_rw reduce_res_type_maxIntOp :
   res_type{ maxIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_maxIntOp :
   arg1_type{ maxIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_maxIntOp :
   arg2_type { maxIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ maxIntOp } >>, reduce_res_type_maxIntOp;
   << arg1_type{ maxIntOp } >>, reduce_arg1_type_maxIntOp;
   << arg2_type{ maxIntOp } >>, reduce_arg2_type_maxIntOp;
]


prim_rw reduce_res_type_eqIntOp :
   res_type{ eqIntOp } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_eqIntOp :
   arg1_type{ eqIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_eqIntOp :
   arg2_type { eqIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ eqIntOp } >>, reduce_res_type_eqIntOp;
   << arg1_type{ eqIntOp } >>, reduce_arg1_type_eqIntOp;
   << arg2_type{ eqIntOp } >>, reduce_arg2_type_eqIntOp;
]


prim_rw reduce_res_type_neqIntOp :
   res_type{ neqIntOp } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_neqIntOp :
   arg1_type{ neqIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_neqIntOp :
   arg2_type { neqIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ neqIntOp } >>, reduce_res_type_neqIntOp;
   << arg1_type{ neqIntOp } >>, reduce_arg1_type_neqIntOp;
   << arg2_type{ neqIntOp } >>, reduce_arg2_type_neqIntOp;
]


prim_rw reduce_res_type_ltIntOp :
   res_type{ ltIntOp } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_ltIntOp :
   arg1_type{ ltIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_ltIntOp :
   arg2_type { ltIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ ltIntOp } >>, reduce_res_type_ltIntOp;
   << arg1_type{ ltIntOp } >>, reduce_arg1_type_ltIntOp;
   << arg2_type{ ltIntOp } >>, reduce_arg2_type_ltIntOp;
]


prim_rw reduce_res_type_leIntOp :
   res_type{ leIntOp } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_leIntOp :
   arg1_type{ leIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_leIntOp :
   arg2_type { leIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ leIntOp } >>, reduce_res_type_leIntOp;
   << arg1_type{ leIntOp } >>, reduce_arg1_type_leIntOp;
   << arg2_type{ leIntOp } >>, reduce_arg2_type_leIntOp;
]


prim_rw reduce_res_type_gtIntOp :
   res_type{ gtIntOp } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_gtIntOp :
   arg1_type{ gtIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_gtIntOp :
   arg2_type { gtIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ gtIntOp } >>, reduce_res_type_gtIntOp;
   << arg1_type{ gtIntOp } >>, reduce_arg1_type_gtIntOp;
   << arg2_type{ gtIntOp } >>, reduce_arg2_type_gtIntOp;
]


prim_rw reduce_res_type_geIntOp :
   res_type{ geIntOp } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_geIntOp :
   arg1_type{ geIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_geIntOp :
   arg2_type { geIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ geIntOp } >>, reduce_res_type_geIntOp;
   << arg1_type{ geIntOp } >>, reduce_arg1_type_geIntOp;
   << arg2_type{ geIntOp } >>, reduce_arg2_type_geIntOp;
]


prim_rw reduce_res_type_cmpIntOp :
   res_type{ cmpIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_cmpIntOp :
   arg1_type{ cmpIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_cmpIntOp :
   arg2_type { cmpIntOp } <-->
   tyInt

let resource reduce += [
   << res_type{ cmpIntOp } >>, reduce_res_type_cmpIntOp;
   << arg1_type{ cmpIntOp } >>, reduce_arg1_type_cmpIntOp;
   << arg2_type{ cmpIntOp } >>, reduce_arg2_type_cmpIntOp;
]


prim_rw reduce_res_type_plusRawIntOp :
   res_type{ plusRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_plusRawIntOp :
   arg1_type{ plusRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_plusRawIntOp :
   arg2_type { plusRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ plusRawIntOp[p:n, s:s] } >>, reduce_res_type_plusRawIntOp;
   << arg1_type{ plusRawIntOp[p:n, s:s] } >>, reduce_arg1_type_plusRawIntOp;
   << arg2_type{ plusRawIntOp[p:n, s:s] } >>, reduce_arg2_type_plusRawIntOp;
]


prim_rw reduce_res_type_minusRawIntOp :
   res_type{ minusRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_minusRawIntOp :
   arg1_type{ minusRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_minusRawIntOp :
   arg2_type { minusRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ minusRawIntOp[p:n, s:s] } >>, reduce_res_type_minusRawIntOp;
   << arg1_type{ minusRawIntOp[p:n, s:s] } >>, reduce_arg1_type_minusRawIntOp;
   << arg2_type{ minusRawIntOp[p:n, s:s] } >>, reduce_arg2_type_minusRawIntOp;
]


prim_rw reduce_res_type_mulRawIntOp :
   res_type{ mulRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_mulRawIntOp :
   arg1_type{ mulRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_mulRawIntOp :
   arg2_type { mulRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ mulRawIntOp[p:n, s:s] } >>, reduce_res_type_mulRawIntOp;
   << arg1_type{ mulRawIntOp[p:n, s:s] } >>, reduce_arg1_type_mulRawIntOp;
   << arg2_type{ mulRawIntOp[p:n, s:s] } >>, reduce_arg2_type_mulRawIntOp;
]


prim_rw reduce_res_type_divRawIntOp :
   res_type{ divRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_divRawIntOp :
   arg1_type{ divRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_divRawIntOp :
   arg2_type { divRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ divRawIntOp[p:n, s:s] } >>, reduce_res_type_divRawIntOp;
   << arg1_type{ divRawIntOp[p:n, s:s] } >>, reduce_arg1_type_divRawIntOp;
   << arg2_type{ divRawIntOp[p:n, s:s] } >>, reduce_arg2_type_divRawIntOp;
]


prim_rw reduce_res_type_remRawIntOp :
   res_type{ remRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_remRawIntOp :
   arg1_type{ remRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_remRawIntOp :
   arg2_type { remRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ remRawIntOp[p:n, s:s] } >>, reduce_res_type_remRawIntOp;
   << arg1_type{ remRawIntOp[p:n, s:s] } >>, reduce_arg1_type_remRawIntOp;
   << arg2_type{ remRawIntOp[p:n, s:s] } >>, reduce_arg2_type_remRawIntOp;
]


prim_rw reduce_res_type_slRawIntOp :
   res_type{ slRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_slRawIntOp :
   arg1_type{ slRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_slRawIntOp :
   arg2_type { slRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ slRawIntOp[p:n, s:s] } >>, reduce_res_type_slRawIntOp;
   << arg1_type{ slRawIntOp[p:n, s:s] } >>, reduce_arg1_type_slRawIntOp;
   << arg2_type{ slRawIntOp[p:n, s:s] } >>, reduce_arg2_type_slRawIntOp;
]


prim_rw reduce_res_type_srRawIntOp :
   res_type{ srRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_srRawIntOp :
   arg1_type{ srRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_srRawIntOp :
   arg2_type { srRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ srRawIntOp[p:n, s:s] } >>, reduce_res_type_srRawIntOp;
   << arg1_type{ srRawIntOp[p:n, s:s] } >>, reduce_arg1_type_srRawIntOp;
   << arg2_type{ srRawIntOp[p:n, s:s] } >>, reduce_arg2_type_srRawIntOp;
]


prim_rw reduce_res_type_andRawIntOp :
   res_type{ andRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_andRawIntOp :
   arg1_type{ andRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_andRawIntOp :
   arg2_type { andRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ andRawIntOp[p:n, s:s] } >>, reduce_res_type_andRawIntOp;
   << arg1_type{ andRawIntOp[p:n, s:s] } >>, reduce_arg1_type_andRawIntOp;
   << arg2_type{ andRawIntOp[p:n, s:s] } >>, reduce_arg2_type_andRawIntOp;
]


prim_rw reduce_res_type_orRawIntOp :
   res_type{ orRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_orRawIntOp :
   arg1_type{ orRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_orRawIntOp :
   arg2_type { orRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ orRawIntOp[p:n, s:s] } >>, reduce_res_type_orRawIntOp;
   << arg1_type{ orRawIntOp[p:n, s:s] } >>, reduce_arg1_type_orRawIntOp;
   << arg2_type{ orRawIntOp[p:n, s:s] } >>, reduce_arg2_type_orRawIntOp;
]


prim_rw reduce_res_type_xorRawIntOp :
   res_type{ xorRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_xorRawIntOp :
   arg1_type{ xorRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_xorRawIntOp :
   arg2_type { xorRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ xorRawIntOp[p:n, s:s] } >>, reduce_res_type_xorRawIntOp;
   << arg1_type{ xorRawIntOp[p:n, s:s] } >>, reduce_arg1_type_xorRawIntOp;
   << arg2_type{ xorRawIntOp[p:n, s:s] } >>, reduce_arg2_type_xorRawIntOp;
]


prim_rw reduce_res_type_maxRawIntOp :
   res_type{ maxRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_maxRawIntOp :
   arg1_type{ maxRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_maxRawIntOp :
   arg2_type { maxRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ maxRawIntOp[p:n, s:s] } >>, reduce_res_type_maxRawIntOp;
   << arg1_type{ maxRawIntOp[p:n, s:s] } >>, reduce_arg1_type_maxRawIntOp;
   << arg2_type{ maxRawIntOp[p:n, s:s] } >>, reduce_arg2_type_maxRawIntOp;
]


prim_rw reduce_res_type_minRawIntOp :
   res_type{ minRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_minRawIntOp :
   arg1_type{ minRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_minRawIntOp :
   arg2_type { minRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ minRawIntOp[p:n, s:s] } >>, reduce_res_type_minRawIntOp;
   << arg1_type{ minRawIntOp[p:n, s:s] } >>, reduce_arg1_type_minRawIntOp;
   << arg2_type{ minRawIntOp[p:n, s:s] } >>, reduce_arg2_type_minRawIntOp;
]


prim_rw reduce_res_type_eqRawIntOp :
   res_type{ eqRawIntOp[p:n, s:s] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_eqRawIntOp :
   arg1_type{ eqRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_eqRawIntOp :
   arg2_type { eqRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ eqRawIntOp[p:n, s:s] } >>, reduce_res_type_eqRawIntOp;
   << arg1_type{ eqRawIntOp[p:n, s:s] } >>, reduce_arg1_type_eqRawIntOp;
   << arg2_type{ eqRawIntOp[p:n, s:s] } >>, reduce_arg2_type_eqRawIntOp;
]


prim_rw reduce_res_type_neqRawIntOp :
   res_type{ neqRawIntOp[p:n, s:s] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_neqRawIntOp :
   arg1_type{ neqRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_neqRawIntOp :
   arg2_type { neqRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ neqRawIntOp[p:n, s:s] } >>, reduce_res_type_neqRawIntOp;
   << arg1_type{ neqRawIntOp[p:n, s:s] } >>, reduce_arg1_type_neqRawIntOp;
   << arg2_type{ neqRawIntOp[p:n, s:s] } >>, reduce_arg2_type_neqRawIntOp;
]


prim_rw reduce_res_type_ltRawIntOp :
   res_type{ ltRawIntOp[p:n, s:s] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_ltRawIntOp :
   arg1_type{ ltRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_ltRawIntOp :
   arg2_type { ltRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ ltRawIntOp[p:n, s:s] } >>, reduce_res_type_ltRawIntOp;
   << arg1_type{ ltRawIntOp[p:n, s:s] } >>, reduce_arg1_type_ltRawIntOp;
   << arg2_type{ ltRawIntOp[p:n, s:s] } >>, reduce_arg2_type_ltRawIntOp;
]


prim_rw reduce_res_type_leRawIntOp :
   res_type{ leRawIntOp[p:n, s:s] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_leRawIntOp :
   arg1_type{ leRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_leRawIntOp :
   arg2_type { leRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ leRawIntOp[p:n, s:s] } >>, reduce_res_type_leRawIntOp;
   << arg1_type{ leRawIntOp[p:n, s:s] } >>, reduce_arg1_type_leRawIntOp;
   << arg2_type{ leRawIntOp[p:n, s:s] } >>, reduce_arg2_type_leRawIntOp;
]


prim_rw reduce_res_type_gtRawIntOp :
   res_type{ gtRawIntOp[p:n, s:s] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_gtRawIntOp :
   arg1_type{ gtRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_gtRawIntOp :
   arg2_type { gtRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ gtRawIntOp[p:n, s:s] } >>, reduce_res_type_gtRawIntOp;
   << arg1_type{ gtRawIntOp[p:n, s:s] } >>, reduce_arg1_type_gtRawIntOp;
   << arg2_type{ gtRawIntOp[p:n, s:s] } >>, reduce_arg2_type_gtRawIntOp;
]


prim_rw reduce_res_type_geRawIntO :
   res_type{ geRawIntOp[p:n, s:s] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_geRawIntO :
   arg1_type{ geRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_geRawIntO :
   arg2_type { geRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ geRawIntOp[p:n, s:s] } >>, reduce_res_type_geRawIntO;
   << arg1_type{ geRawIntOp[p:n, s:s] } >>, reduce_arg1_type_geRawIntO;
   << arg2_type{ geRawIntOp[p:n, s:s] } >>, reduce_arg2_type_geRawIntO;
]


prim_rw reduce_res_type_cmpRawIntOp :
   res_type{ cmpRawIntOp[p:n, s:s] } <-->
   tyInt

prim_rw reduce_arg1_type_cmpRawIntOp :
   arg1_type{ cmpRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_cmpRawIntOp :
   arg2_type { cmpRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

let resource reduce += [
   << res_type{ cmpRawIntOp[p:n, s:s] } >>, reduce_res_type_cmpRawIntOp;
   << arg1_type{ cmpRawIntOp[p:n, s:s] } >>, reduce_arg1_type_cmpRawIntOp;
   << arg2_type{ cmpRawIntOp[p:n, s:s] } >>, reduce_arg2_type_cmpRawIntOp;
]


prim_rw reduce_res_type_plusFloatOp :
   res_type{ plusFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_plusFloatOp :
   arg1_type{ plusFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_plusFloatOp :
   arg2_type { plusFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ plusFloatOp[p:n] } >>, reduce_res_type_plusFloatOp;
   << arg1_type{ plusFloatOp[p:n] } >>, reduce_arg1_type_plusFloatOp;
   << arg2_type{ plusFloatOp[p:n] } >>, reduce_arg2_type_plusFloatOp;
]


prim_rw reduce_res_type_minusFloatOp :
   res_type{ minusFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_minusFloatOp :
   arg1_type{ minusFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_minusFloatOp :
   arg2_type { minusFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ minusFloatOp[p:n] } >>, reduce_res_type_minusFloatOp;
   << arg1_type{ minusFloatOp[p:n] } >>, reduce_arg1_type_minusFloatOp;
   << arg2_type{ minusFloatOp[p:n] } >>, reduce_arg2_type_minusFloatOp;
]


prim_rw reduce_res_type_mulFloatOp :
   res_type{ mulFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_mulFloatOp :
   arg1_type{ mulFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_mulFloatOp :
   arg2_type { mulFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ mulFloatOp[p:n] } >>, reduce_res_type_mulFloatOp;
   << arg1_type{ mulFloatOp[p:n] } >>, reduce_arg1_type_mulFloatOp;
   << arg2_type{ mulFloatOp[p:n] } >>, reduce_arg2_type_mulFloatOp;
]


prim_rw reduce_res_type_divFloatOp :
   res_type{ divFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_divFloatOp :
   arg1_type{ divFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_divFloatOp :
   arg2_type { divFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ divFloatOp[p:n] } >>, reduce_res_type_divFloatOp;
   << arg1_type{ divFloatOp[p:n] } >>, reduce_arg1_type_divFloatOp;
   << arg2_type{ divFloatOp[p:n] } >>, reduce_arg2_type_divFloatOp;
]


prim_rw reduce_res_type_remFloatOp :
   res_type{ remFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_remFloatOp :
   arg1_type{ remFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_remFloatOp :
   arg2_type { remFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ remFloatOp[p:n] } >>, reduce_res_type_remFloatOp;
   << arg1_type{ remFloatOp[p:n] } >>, reduce_arg1_type_remFloatOp;
   << arg2_type{ remFloatOp[p:n] } >>, reduce_arg2_type_remFloatOp;
]


prim_rw reduce_res_type_maxFloatOp :
   res_type{ maxFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_maxFloatOp :
   arg1_type{ maxFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_maxFloatOp :
   arg2_type { maxFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ maxFloatOp[p:n] } >>, reduce_res_type_maxFloatOp;
   << arg1_type{ maxFloatOp[p:n] } >>, reduce_arg1_type_maxFloatOp;
   << arg2_type{ maxFloatOp[p:n] } >>, reduce_arg2_type_maxFloatOp;
]


prim_rw reduce_res_type_minFloatOp :
   res_type{ minFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_minFloatOp :
   arg1_type{ minFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_minFloatOp :
   arg2_type { minFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ minFloatOp[p:n] } >>, reduce_res_type_minFloatOp;
   << arg1_type{ minFloatOp[p:n] } >>, reduce_arg1_type_minFloatOp;
   << arg2_type{ minFloatOp[p:n] } >>, reduce_arg2_type_minFloatOp;
]


prim_rw reduce_res_type_eqFloatOp :
   res_type{ eqFloatOp[p:n] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_eqFloatOp :
   arg1_type{ eqFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_eqFloatOp :
   arg2_type { eqFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ eqFloatOp[p:n] } >>, reduce_res_type_eqFloatOp;
   << arg1_type{ eqFloatOp[p:n] } >>, reduce_arg1_type_eqFloatOp;
   << arg2_type{ eqFloatOp[p:n] } >>, reduce_arg2_type_eqFloatOp;
]


prim_rw reduce_res_type_neqFloatOp :
   res_type{ neqFloatOp[p:n] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_neqFloatOp :
   arg1_type{ neqFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_neqFloatOp :
   arg2_type { neqFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ neqFloatOp[p:n] } >>, reduce_res_type_neqFloatOp;
   << arg1_type{ neqFloatOp[p:n] } >>, reduce_arg1_type_neqFloatOp;
   << arg2_type{ neqFloatOp[p:n] } >>, reduce_arg2_type_neqFloatOp;
]


prim_rw reduce_res_type_ltFloatOp :
   res_type{ ltFloatOp[p:n] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_ltFloatOp :
   arg1_type{ ltFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_ltFloatOp :
   arg2_type { ltFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ ltFloatOp[p:n] } >>, reduce_res_type_ltFloatOp;
   << arg1_type{ ltFloatOp[p:n] } >>, reduce_arg1_type_ltFloatOp;
   << arg2_type{ ltFloatOp[p:n] } >>, reduce_arg2_type_ltFloatOp;
]


prim_rw reduce_res_type_leFloatOp :
   res_type{ leFloatOp[p:n] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_leFloatOp :
   arg1_type{ leFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_leFloatOp :
   arg2_type { leFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ leFloatOp[p:n] } >>, reduce_res_type_leFloatOp;
   << arg1_type{ leFloatOp[p:n] } >>, reduce_arg1_type_leFloatOp;
   << arg2_type{ leFloatOp[p:n] } >>, reduce_arg2_type_leFloatOp;
]


prim_rw reduce_res_type_gtFloatOp :
   res_type{ gtFloatOp[p:n] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_gtFloatOp :
   arg1_type{ gtFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_gtFloatOp :
   arg2_type { gtFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ gtFloatOp[p:n] } >>, reduce_res_type_gtFloatOp;
   << arg1_type{ gtFloatOp[p:n] } >>, reduce_arg1_type_gtFloatOp;
   << arg2_type{ gtFloatOp[p:n] } >>, reduce_arg2_type_gtFloatOp;
]


prim_rw reduce_res_type_geFloatOp :
   res_type{ geFloatOp[p:n] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_geFloatOp :
   arg1_type{ geFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_geFloatOp :
   arg2_type { geFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ geFloatOp[p:n] } >>, reduce_res_type_geFloatOp;
   << arg1_type{ geFloatOp[p:n] } >>, reduce_arg1_type_geFloatOp;
   << arg2_type{ geFloatOp[p:n] } >>, reduce_arg2_type_geFloatOp;
]


prim_rw reduce_res_type_cmpFloatOp :
   res_type{ cmpFloatOp[p:n] } <-->
   tyInt

prim_rw reduce_arg1_type_cmpFloatOp :
   arg1_type{ cmpFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_cmpFloatOp :
   arg2_type { cmpFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ cmpFloatOp[p:n] } >>, reduce_res_type_cmpFloatOp;
   << arg1_type{ cmpFloatOp[p:n] } >>, reduce_arg1_type_cmpFloatOp;
   << arg2_type{ cmpFloatOp[p:n] } >>, reduce_arg2_type_cmpFloatOp;
]


prim_rw reduce_res_type_atan2FloatOp :
   res_type{ atan2FloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_atan2FloatOp :
   arg1_type{ atan2FloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_atan2FloatOp :
   arg2_type { atan2FloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ atan2FloatOp[p:n] } >>, reduce_res_type_atan2FloatOp;
   << arg1_type{ atan2FloatOp[p:n] } >>, reduce_arg1_type_atan2FloatOp;
   << arg2_type{ atan2FloatOp[p:n] } >>, reduce_arg2_type_atan2FloatOp;
]


prim_rw reduce_res_type_powerFloatOp :
   res_type{ powerFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_powerFloatOp :
   arg1_type{ powerFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_powerFloatOp :
   arg2_type { powerFloatOp[p:n] } <-->
   tyFloat[p:n]

let resource reduce += [
   << res_type{ powerFloatOp[p:n] } >>, reduce_res_type_powerFloatOp;
   << arg1_type{ powerFloatOp[p:n] } >>, reduce_arg1_type_powerFloatOp;
   << arg2_type{ powerFloatOp[p:n] } >>, reduce_arg2_type_powerFloatOp;
]


prim_rw reduce_res_type_ldExpFloatIntOp :
   res_type{ ldExpFloatIntOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_ldExpFloatIntOp :
   arg1_type{ ldExpFloatIntOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_ldExpFloatIntOp :
   arg2_type { ldExpFloatIntOp[p:n] } <-->
   tyInt

let resource reduce += [
   << res_type{ ldExpFloatIntOp[p:n] } >>, reduce_res_type_ldExpFloatIntOp;
   << arg1_type{ ldExpFloatIntOp[p:n] } >>, reduce_arg1_type_ldExpFloatIntOp;
   << arg2_type{ ldExpFloatIntOp[p:n] } >>, reduce_arg2_type_ldExpFloatIntOp;
]


prim_rw reduce_res_type_eqEqOp :
   res_type{ eqEqOp{ 'ty } } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_eqEqOp :
   arg1_type{ eqEqOp{ 'ty } } <-->
   'ty

prim_rw reduce_arg2_type_eqEqOp :
   arg2_type { eqEqOp{ 'ty } } <-->
   'ty

let resource reduce += [
   << res_type{ eqEqOp{ 'ty } } >>, reduce_res_type_eqEqOp;
   << arg1_type{ eqEqOp{ 'ty } } >>, reduce_arg1_type_eqEqOp;
   << arg2_type{ eqEqOp{ 'ty } } >>, reduce_arg2_type_eqEqOp;
]


prim_rw reduce_res_type_neqEqOp :
   res_type{ neqEqOp{ 'ty } } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_neqEqOp :
   arg1_type{ neqEqOp{ 'ty } } <-->
   'ty

prim_rw reduce_arg2_type_neqEqOp :
   arg2_type { neqEqOp{ 'ty } } <-->
   'ty

let resource reduce += [
   << res_type{ neqEqOp{ 'ty } } >>, reduce_res_type_neqEqOp;
   << arg1_type{ neqEqOp{ 'ty } } >>, reduce_arg1_type_neqEqOp;
   << arg2_type{ neqEqOp{ 'ty } } >>, reduce_arg2_type_neqEqOp;
]
