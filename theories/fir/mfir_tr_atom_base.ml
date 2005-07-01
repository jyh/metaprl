doc <:doc<
   @module[Mfir_tr_atom_base]

   The @tt[Mfir_tr_atom_base] module defines the argument types
   and result types of the FIR operators.

   @docoff
   ------------------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.  Additional
   information about the system is available at
   http://www.metaprl.org/

   Copyright (C) 2002 Brian Emre Aydemir, Caltech

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

   Author: Brian Emre Aydemir
   @email{emre@cs.caltech.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>

extends Mfir_ty
extends Mfir_exp
extends Mfir_option
extends Mfir_sequent


(**************************************************************************
 * Declarations.
 **************************************************************************)

doc <:doc<
   @terms

   The term @tt[res_type] returns the result type of an operator @tt[op].
   The terms @tt[arg1_type] and @tt[arg2_type] return the types of
   first and second arguments of an operator @tt[op] (@tt[arg2_type] is
   undefined if @tt[op] is a unary operator).
>>

declare res_type{ 'op }
declare arg1_type{ 'op }
declare arg2_type{ 'op }

doc docoff

open Top_conversionals

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

doc <:doc<
   @rewrites

   Rewrites are used to define the argument and result types of the
   FIR unary and binary operators.  The types may not be well-formed
   if the original operator is not well-formed.  We omit an explicit
   listing of these rewrites.
>>

doc docoff

prim_rw reduce_res_type_notEnumOp {| reduce |} :
   res_type{ notEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_arg1_type_notEnumOp {| reduce |} :
   arg1_type{ notEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_res_type_uminusIntOp {| reduce |} :
   res_type{ uminusIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_uminusIntOp {| reduce |} :
   arg1_type{ uminusIntOp } <-->
   tyInt

prim_rw reduce_res_type_notIntOp {| reduce |} :
   res_type{ notIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_notIntOp {| reduce |} :
   arg1_type{ notIntOp } <-->
   tyInt

prim_rw reduce_res_type_absIntOp {| reduce |} :
   res_type{ absIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_absIntOp {| reduce |} :
   arg1_type{ absIntOp } <-->
   tyInt

prim_rw reduce_res_type_uminusRawIntOp {| reduce |} :
   res_type{ uminusRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_uminusRawIntOp {| reduce |} :
   arg1_type{ uminusRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_notRawIntOp {| reduce |} :
   res_type{ notRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_notRawIntOp {| reduce |} :
   arg1_type{ notRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_uminusFloatOp {| reduce |} :
   res_type{ uminusFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_uminusFloatOp {| reduce |} :
   arg1_type{ uminusFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_absFloatOp {| reduce |} :
   res_type{ absFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_absFloatOp {| reduce |} :
   arg1_type{ absFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_sinFloatOp {| reduce |} :
   res_type{ sinFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_sinFloatOp {| reduce |} :
   arg1_type{ sinFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_cosFloatOp {| reduce |} :
   res_type{ cosFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_cosFloatOp {| reduce |} :
   arg1_type{ cosFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_tanFloatop {| reduce |} :
   res_type{ tanFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_tanFloatop {| reduce |} :
   arg1_type{ tanFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_asinFloatOp {| reduce |} :
   res_type{ asinFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_asinFloatOp {| reduce |} :
   arg1_type{ asinFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_atanFloatOp {| reduce |} :
   res_type{ atanFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_atanFloatOp {| reduce |} :
   arg1_type{ atanFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_sinhFloatOp {| reduce |} :
   res_type{ sinhFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_sinhFloatOp {| reduce |} :
   arg1_type{ sinhFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_coshFloatOp {| reduce |} :
   res_type{ coshFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_coshFloatOp {| reduce |} :
   arg1_type{ coshFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_tanhFloatOp {| reduce |} :
   res_type{ tanhFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_tanhFloatOp {| reduce |} :
   arg1_type{ tanhFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_expFloatOp {| reduce |} :
   res_type{ expFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_expFloatOp {| reduce |} :
   arg1_type{ expFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_logFloatOp {| reduce |} :
   res_type{ logFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_logFloatOp {| reduce |} :
   arg1_type{ logFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_sqrtFloatOp {| reduce |} :
   res_type{ sqrtFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_sqrtFloatOp {| reduce |} :
   arg1_type{ sqrtFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_ceilFloatOp {| reduce |} :
   res_type{ ceilFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_ceilFloatOp {| reduce |} :
   arg1_type{ ceilFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_floorFloatOp {| reduce |} :
   res_type{ floorFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_floorFloatOp {| reduce |} :
   arg1_type{ floorFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_intOfFloatOp {| reduce |} :
   res_type{ intOfFloatOp[p:n] } <-->
   tyInt

prim_rw reduce_arg1_type_intOfFloatOp {| reduce |} :
   arg1_type{ intOfFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_intOfRawIntOp {| reduce |} :
   res_type{ intOfRawIntOp[p:n, s:s] } <-->
   tyInt

prim_rw reduce_arg1_type_intOfRawIntOp {| reduce |} :
   arg1_type{ intOfRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_floatOfIntOp {| reduce |} :
   res_type{ floatOfIntOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_floatOfIntOp {| reduce |} :
   arg1_type{ floatOfIntOp[p:n] } <-->
   tyInt

prim_rw reduce_res_type_floatOfFloatOp {| reduce |} :
   res_type{ floatOfFloatOp[p1:n, p2:n] } <-->
   tyFloat[p1:n]

prim_rw reduce_arg1_type_floatOfFloatOp {| reduce |} :
   arg1_type{ floatOfFloatOp[p1:n, p2:n] } <-->
   tyFloat[p2:n]

prim_rw reduce_res_type_floatOfRawIntOp {| reduce |} :
   res_type{ floatOfRawIntOp[fp:n, rp:n, s:s] } <-->
   tyFloat[fp:n]

prim_rw reduce_arg1_type_floatOfRawIntOp {| reduce |} :
   arg1_type{ floatOfRawIntOp[fp:n, rp:n, s:s] } <-->
   tyRawInt[rp:n, s:s]

prim_rw reduce_res_type_rawIntOfIntOp {| reduce |} :
   res_type{ rawIntOfIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_rawIntOfIntOp {| reduce |} :
   arg1_type{ rawIntOfIntOp[p:n, s:s] } <-->
   tyInt

prim_rw reduce_res_type_rawIntOfEnumOp {| reduce |} :
   res_type{ rawIntOfEnumOp[p:n, s:s, i:n] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_rawIntOfEnumOp {| reduce |} :
   arg1_type{ rawIntOfEnumOp[p:n, s:s, i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_res_type_rawIntOfFloatOp {| reduce |} :
   res_type{ rawIntOfFloatOp[rp:n, s:s, fp:n] } <-->
   tyRawInt[rp:n, s:s]

prim_rw reduce_arg1_type_rawIntOfFloatOp {| reduce |} :
   arg1_type{ rawIntOfFloatOp[rp:n, s:s, fp:n] } <-->
   tyFloat[fp:n]

prim_rw reduce_res_type_rawIntOfRawIntOp {| reduce |} :
   res_type{ rawIntOfRawIntOp[dp:n, ds:s, sp:n, ss:s] } <-->
   tyRawInt[dp:n, ds:s]

prim_rw reduce_arg1_type_rawIntOfRawIntOp {| reduce |} :
   arg1_type{ rawIntOfRawIntOp[dp:n, ds:s, sp:n, ss:s] } <-->
   tyRawInt[sp:n, ss:s]

prim_rw reduce_res_type_dtupleOfDTupleOp {| reduce |} :
   res_type{ dtupleOfDTupleOp{ 'tv; 'mtyl } } <-->
   tyDTuple{ 'tv; none }

prim_rw reduce_arg1_type_dtupleOfDTupleOp {| reduce |} :
   arg1_type{ dtupleOfDTupleOp{ 'tv; 'mtyl } } <-->
   tyDTuple{ 'tv; some{ 'mtyl } }

prim_rw reduce_res_type_unionOfUnionOp {| reduce |} :
   res_type{ unionOfUnionOp{ 'tv; 'tyl; 's1; 's2 } } <-->
   tyUnion{ 'tv; 'tyl; 's1 }

prim_rw reduce_arg1_type_unionOfUnionOp {| reduce |} :
   arg1_type{ unionOfUnionOp{ 'tv; 'tyl; 's1; 's2 } } <-->
   tyUnion{ 'tv; 'tyl; 's2 }

prim_rw reduce_res_type_rawDataOfFrameOp {| reduce |} :
   res_type{ rawDataOfFrameOp{ 'tv; 'tyl } } <-->
   tyRawData

prim_rw reduce_arg1_type_rawDataOfFrameOp {| reduce |} :
   arg1_type{ rawDataOfFrameOp{ 'tv; 'tyl } } <-->
   tyFrame{ 'tv; 'tyl }

prim_rw reduce_res_type_andEnumOp {| reduce |} :
   res_type{ andEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_arg1_type_andEnumOp {| reduce |} :
   arg1_type{ andEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_arg2_type_andEnumOp {| reduce |} :
   arg2_type { andEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_res_type_orEnumOp {| reduce |} :
   res_type{ orEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_arg1_type_orEnumOp {| reduce |} :
   arg1_type{ orEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_arg2_type_orEnumOp {| reduce |} :
   arg2_type { orEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_res_type_xorEnumOp {| reduce |} :
   res_type{ xorEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_arg1_type_xorEnumOp {| reduce |} :
   arg1_type{ xorEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_arg2_type_xorEnumOp {| reduce |} :
   arg2_type { xorEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_res_type_plusIntOp {| reduce |} :
   res_type{ plusIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_plusIntOp {| reduce |} :
   arg1_type{ plusIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_plusIntOp {| reduce |} :
   arg2_type { plusIntOp } <-->
   tyInt

prim_rw reduce_res_type_minusIntOp {| reduce |} :
   res_type{ minusIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_minusIntOp {| reduce |} :
   arg1_type{ minusIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_minusIntOp {| reduce |} :
   arg2_type { minusIntOp } <-->
   tyInt

prim_rw reduce_res_type_mulIntOp {| reduce |} :
   res_type{ mulIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_mulIntOp {| reduce |} :
   arg1_type{ mulIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_mulIntOp {| reduce |} :
   arg2_type { mulIntOp } <-->
   tyInt

prim_rw reduce_res_type_divIntOp {| reduce |} :
   res_type{ divIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_divIntOp {| reduce |} :
   arg1_type{ divIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_divIntOp {| reduce |} :
   arg2_type { divIntOp } <-->
   tyInt

prim_rw reduce_res_type_remIntOp {| reduce |} :
   res_type{ remIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_remIntOp {| reduce |} :
   arg1_type{ remIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_remIntOp {| reduce |} :
   arg2_type { remIntOp } <-->
   tyInt

prim_rw reduce_res_type_lslIntOp {| reduce |} :
   res_type{ lslIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_lslIntOp {| reduce |} :
   arg1_type{ lslIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_lslIntOp {| reduce |} :
   arg2_type { lslIntOp } <-->
   tyInt

prim_rw reduce_res_type_lsrIntOp {| reduce |} :
   res_type{ lsrIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_lsrIntOp {| reduce |} :
   arg1_type{ lsrIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_lsrIntOp {| reduce |} :
   arg2_type { lsrIntOp } <-->
   tyInt

prim_rw reduce_res_type_asrIntOp {| reduce |} :
   res_type{ asrIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_asrIntOp {| reduce |} :
   arg1_type{ asrIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_asrIntOp {| reduce |} :
   arg2_type { asrIntOp } <-->
   tyInt

prim_rw reduce_res_type_andIntOp {| reduce |} :
   res_type{ andIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_andIntOp {| reduce |} :
   arg1_type{ andIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_andIntOp {| reduce |} :
   arg2_type { andIntOp } <-->
   tyInt

prim_rw reduce_res_type_orIntOp {| reduce |} :
   res_type{ orIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_orIntOp {| reduce |} :
   arg1_type{ orIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_orIntOp {| reduce |} :
   arg2_type { orIntOp } <-->
   tyInt

prim_rw reduce_res_type_xorIntOp {| reduce |} :
   res_type{ xorIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_xorIntOp {| reduce |} :
   arg1_type{ xorIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_xorIntOp {| reduce |} :
   arg2_type { xorIntOp } <-->
   tyInt

prim_rw reduce_res_type_maxIntOp {| reduce |} :
   res_type{ maxIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_maxIntOp {| reduce |} :
   arg1_type{ maxIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_maxIntOp {| reduce |} :
   arg2_type { maxIntOp } <-->
   tyInt

prim_rw reduce_res_type_eqIntOp {| reduce |} :
   res_type{ eqIntOp } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_eqIntOp {| reduce |} :
   arg1_type{ eqIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_eqIntOp {| reduce |} :
   arg2_type { eqIntOp } <-->
   tyInt

prim_rw reduce_res_type_neqIntOp {| reduce |} :
   res_type{ neqIntOp } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_neqIntOp {| reduce |} :
   arg1_type{ neqIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_neqIntOp {| reduce |} :
   arg2_type { neqIntOp } <-->
   tyInt

prim_rw reduce_res_type_ltIntOp {| reduce |} :
   res_type{ ltIntOp } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_ltIntOp {| reduce |} :
   arg1_type{ ltIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_ltIntOp {| reduce |} :
   arg2_type { ltIntOp } <-->
   tyInt

prim_rw reduce_res_type_leIntOp {| reduce |} :
   res_type{ leIntOp } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_leIntOp {| reduce |} :
   arg1_type{ leIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_leIntOp {| reduce |} :
   arg2_type { leIntOp } <-->
   tyInt

prim_rw reduce_res_type_gtIntOp {| reduce |} :
   res_type{ gtIntOp } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_gtIntOp {| reduce |} :
   arg1_type{ gtIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_gtIntOp {| reduce |} :
   arg2_type { gtIntOp } <-->
   tyInt

prim_rw reduce_res_type_geIntOp {| reduce |} :
   res_type{ geIntOp } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_geIntOp {| reduce |} :
   arg1_type{ geIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_geIntOp {| reduce |} :
   arg2_type { geIntOp } <-->
   tyInt

prim_rw reduce_res_type_cmpIntOp {| reduce |} :
   res_type{ cmpIntOp } <-->
   tyInt

prim_rw reduce_arg1_type_cmpIntOp {| reduce |} :
   arg1_type{ cmpIntOp } <-->
   tyInt

prim_rw reduce_arg2_type_cmpIntOp {| reduce |} :
   arg2_type { cmpIntOp } <-->
   tyInt

prim_rw reduce_res_type_plusRawIntOp {| reduce |} :
   res_type{ plusRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_plusRawIntOp {| reduce |} :
   arg1_type{ plusRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_plusRawIntOp {| reduce |} :
   arg2_type { plusRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_minusRawIntOp {| reduce |} :
   res_type{ minusRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_minusRawIntOp {| reduce |} :
   arg1_type{ minusRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_minusRawIntOp {| reduce |} :
   arg2_type { minusRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_mulRawIntOp {| reduce |} :
   res_type{ mulRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_mulRawIntOp {| reduce |} :
   arg1_type{ mulRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_mulRawIntOp {| reduce |} :
   arg2_type { mulRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_divRawIntOp {| reduce |} :
   res_type{ divRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_divRawIntOp {| reduce |} :
   arg1_type{ divRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_divRawIntOp {| reduce |} :
   arg2_type { divRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_remRawIntOp {| reduce |} :
   res_type{ remRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_remRawIntOp {| reduce |} :
   arg1_type{ remRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_remRawIntOp {| reduce |} :
   arg2_type { remRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_slRawIntOp {| reduce |} :
   res_type{ slRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_slRawIntOp {| reduce |} :
   arg1_type{ slRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_slRawIntOp {| reduce |} :
   arg2_type { slRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_srRawIntOp {| reduce |} :
   res_type{ srRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_srRawIntOp {| reduce |} :
   arg1_type{ srRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_srRawIntOp {| reduce |} :
   arg2_type { srRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_andRawIntOp {| reduce |} :
   res_type{ andRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_andRawIntOp {| reduce |} :
   arg1_type{ andRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_andRawIntOp {| reduce |} :
   arg2_type { andRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_orRawIntOp {| reduce |} :
   res_type{ orRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_orRawIntOp {| reduce |} :
   arg1_type{ orRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_orRawIntOp {| reduce |} :
   arg2_type { orRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_xorRawIntOp {| reduce |} :
   res_type{ xorRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_xorRawIntOp {| reduce |} :
   arg1_type{ xorRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_xorRawIntOp {| reduce |} :
   arg2_type { xorRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_maxRawIntOp {| reduce |} :
   res_type{ maxRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_maxRawIntOp {| reduce |} :
   arg1_type{ maxRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_maxRawIntOp {| reduce |} :
   arg2_type { maxRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_minRawIntOp {| reduce |} :
   res_type{ minRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg1_type_minRawIntOp {| reduce |} :
   arg1_type{ minRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_minRawIntOp {| reduce |} :
   arg2_type { minRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_eqRawIntOp {| reduce |} :
   res_type{ eqRawIntOp[p:n, s:s] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_eqRawIntOp {| reduce |} :
   arg1_type{ eqRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_eqRawIntOp {| reduce |} :
   arg2_type { eqRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_neqRawIntOp {| reduce |} :
   res_type{ neqRawIntOp[p:n, s:s] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_neqRawIntOp {| reduce |} :
   arg1_type{ neqRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_neqRawIntOp {| reduce |} :
   arg2_type { neqRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_ltRawIntOp {| reduce |} :
   res_type{ ltRawIntOp[p:n, s:s] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_ltRawIntOp {| reduce |} :
   arg1_type{ ltRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_ltRawIntOp {| reduce |} :
   arg2_type { ltRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_leRawIntOp {| reduce |} :
   res_type{ leRawIntOp[p:n, s:s] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_leRawIntOp {| reduce |} :
   arg1_type{ leRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_leRawIntOp {| reduce |} :
   arg2_type { leRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_gtRawIntOp {| reduce |} :
   res_type{ gtRawIntOp[p:n, s:s] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_gtRawIntOp {| reduce |} :
   arg1_type{ gtRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_gtRawIntOp {| reduce |} :
   arg2_type { gtRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_geRawIntO {| reduce |} :
   res_type{ geRawIntOp[p:n, s:s] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_geRawIntO {| reduce |} :
   arg1_type{ geRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_geRawIntO {| reduce |} :
   arg2_type { geRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_cmpRawIntOp {| reduce |} :
   res_type{ cmpRawIntOp[p:n, s:s] } <-->
   tyInt

prim_rw reduce_arg1_type_cmpRawIntOp {| reduce |} :
   arg1_type{ cmpRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_arg2_type_cmpRawIntOp {| reduce |} :
   arg2_type { cmpRawIntOp[p:n, s:s] } <-->
   tyRawInt[p:n, s:s]

prim_rw reduce_res_type_plusFloatOp {| reduce |} :
   res_type{ plusFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_plusFloatOp {| reduce |} :
   arg1_type{ plusFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_plusFloatOp {| reduce |} :
   arg2_type { plusFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_minusFloatOp {| reduce |} :
   res_type{ minusFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_minusFloatOp {| reduce |} :
   arg1_type{ minusFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_minusFloatOp {| reduce |} :
   arg2_type { minusFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_mulFloatOp {| reduce |} :
   res_type{ mulFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_mulFloatOp {| reduce |} :
   arg1_type{ mulFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_mulFloatOp {| reduce |} :
   arg2_type { mulFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_divFloatOp {| reduce |} :
   res_type{ divFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_divFloatOp {| reduce |} :
   arg1_type{ divFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_divFloatOp {| reduce |} :
   arg2_type { divFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_remFloatOp {| reduce |} :
   res_type{ remFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_remFloatOp {| reduce |} :
   arg1_type{ remFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_remFloatOp {| reduce |} :
   arg2_type { remFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_maxFloatOp {| reduce |} :
   res_type{ maxFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_maxFloatOp {| reduce |} :
   arg1_type{ maxFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_maxFloatOp {| reduce |} :
   arg2_type { maxFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_minFloatOp {| reduce |} :
   res_type{ minFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_minFloatOp {| reduce |} :
   arg1_type{ minFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_minFloatOp {| reduce |} :
   arg2_type { minFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_eqFloatOp {| reduce |} :
   res_type{ eqFloatOp[p:n] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_eqFloatOp {| reduce |} :
   arg1_type{ eqFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_eqFloatOp {| reduce |} :
   arg2_type { eqFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_neqFloatOp {| reduce |} :
   res_type{ neqFloatOp[p:n] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_neqFloatOp {| reduce |} :
   arg1_type{ neqFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_neqFloatOp {| reduce |} :
   arg2_type { neqFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_ltFloatOp {| reduce |} :
   res_type{ ltFloatOp[p:n] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_ltFloatOp {| reduce |} :
   arg1_type{ ltFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_ltFloatOp {| reduce |} :
   arg2_type { ltFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_leFloatOp {| reduce |} :
   res_type{ leFloatOp[p:n] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_leFloatOp {| reduce |} :
   arg1_type{ leFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_leFloatOp {| reduce |} :
   arg2_type { leFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_gtFloatOp {| reduce |} :
   res_type{ gtFloatOp[p:n] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_gtFloatOp {| reduce |} :
   arg1_type{ gtFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_gtFloatOp {| reduce |} :
   arg2_type { gtFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_geFloatOp {| reduce |} :
   res_type{ geFloatOp[p:n] } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_geFloatOp {| reduce |} :
   arg1_type{ geFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_geFloatOp {| reduce |} :
   arg2_type { geFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_cmpFloatOp {| reduce |} :
   res_type{ cmpFloatOp[p:n] } <-->
   tyInt

prim_rw reduce_arg1_type_cmpFloatOp {| reduce |} :
   arg1_type{ cmpFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_cmpFloatOp {| reduce |} :
   arg2_type { cmpFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_atan2FloatOp {| reduce |} :
   res_type{ atan2FloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_atan2FloatOp {| reduce |} :
   arg1_type{ atan2FloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_atan2FloatOp {| reduce |} :
   arg2_type { atan2FloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_powerFloatOp {| reduce |} :
   res_type{ powerFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_powerFloatOp {| reduce |} :
   arg1_type{ powerFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_powerFloatOp {| reduce |} :
   arg2_type { powerFloatOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_res_type_ldExpFloatIntOp {| reduce |} :
   res_type{ ldExpFloatIntOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg1_type_ldExpFloatIntOp {| reduce |} :
   arg1_type{ ldExpFloatIntOp[p:n] } <-->
   tyFloat[p:n]

prim_rw reduce_arg2_type_ldExpFloatIntOp {| reduce |} :
   arg2_type { ldExpFloatIntOp[p:n] } <-->
   tyInt

prim_rw reduce_res_type_eqEqOp {| reduce |} :
   res_type{ eqEqOp{ 'ty } } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_eqEqOp {| reduce |} :
   arg1_type{ eqEqOp{ 'ty } } <-->
   'ty

prim_rw reduce_arg2_type_eqEqOp {| reduce |} :
   arg2_type { eqEqOp{ 'ty } } <-->
   'ty

prim_rw reduce_res_type_neqEqOp {| reduce |} :
   res_type{ neqEqOp{ 'ty } } <-->
   tyEnum[2]

prim_rw reduce_arg1_type_neqEqOp {| reduce |} :
   arg1_type{ neqEqOp{ 'ty } } <-->
   'ty

prim_rw reduce_arg2_type_neqEqOp {| reduce |} :
   arg2_type { neqEqOp{ 'ty } } <-->
   'ty

