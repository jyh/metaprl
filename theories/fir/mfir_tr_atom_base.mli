(*
 * The Mfir_tr_atom_base module defines the argument types
 * and result types of the FIR operators.
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

extends Mfir_ty
extends Mfir_exp
extends Mfir_sequent

open Tactic_type.Conversionals


(**************************************************************************
 * Declarations.
 **************************************************************************)

declare res_type{ 'op }
declare arg1_type{ 'op }
declare arg2_type{ 'op }


(**************************************************************************
 * Rewrites.
 **************************************************************************)

topval reduce_res_type_notEnumOp : conv
topval reduce_arg1_type_notEnumOp : conv

topval reduce_res_type_uminusIntOp : conv
topval reduce_arg1_type_uminusIntOp : conv

topval reduce_res_type_notIntOp : conv
topval reduce_arg1_type_notIntOp : conv

topval reduce_res_type_absIntOp : conv
topval reduce_arg1_type_absIntOp : conv

topval reduce_res_type_uminusRawIntOp : conv
topval reduce_arg1_type_uminusRawIntOp : conv

topval reduce_res_type_notRawIntOp : conv
topval reduce_arg1_type_notRawIntOp : conv

topval reduce_res_type_uminusFloatOp : conv
topval reduce_arg1_type_uminusFloatOp : conv

topval reduce_res_type_absFloatOp : conv
topval reduce_arg1_type_absFloatOp : conv

topval reduce_res_type_sinFloatOp : conv
topval reduce_arg1_type_sinFloatOp : conv

topval reduce_res_type_cosFloatOp : conv
topval reduce_arg1_type_cosFloatOp : conv

topval reduce_res_type_tanFloatop : conv
topval reduce_arg1_type_tanFloatop : conv

topval reduce_res_type_asinFloatOp : conv
topval reduce_arg1_type_asinFloatOp : conv

topval reduce_res_type_atanFloatOp : conv
topval reduce_arg1_type_atanFloatOp : conv

topval reduce_res_type_sinhFloatOp : conv
topval reduce_arg1_type_sinhFloatOp : conv

topval reduce_res_type_coshFloatOp : conv
topval reduce_arg1_type_coshFloatOp : conv

topval reduce_res_type_tanhFloatOp : conv
topval reduce_arg1_type_tanhFloatOp : conv

topval reduce_res_type_expFloatOp : conv
topval reduce_arg1_type_expFloatOp : conv

topval reduce_res_type_logFloatOp : conv
topval reduce_arg1_type_logFloatOp : conv

topval reduce_res_type_sqrtFloatOp : conv
topval reduce_arg1_type_sqrtFloatOp : conv

topval reduce_res_type_ceilFloatOp : conv
topval reduce_arg1_type_ceilFloatOp : conv

topval reduce_res_type_floorFloatOp : conv
topval reduce_arg1_type_floorFloatOp : conv

topval reduce_res_type_intOfFloatOp : conv
topval reduce_arg1_type_intOfFloatOp : conv

topval reduce_res_type_intOfRawIntOp : conv
topval reduce_arg1_type_intOfRawIntOp : conv

topval reduce_res_type_floatOfIntOp : conv
topval reduce_arg1_type_floatOfIntOp : conv

topval reduce_res_type_floatOfFloatOp : conv
topval reduce_arg1_type_floatOfFloatOp : conv

topval reduce_res_type_floatOfRawIntOp : conv
topval reduce_arg1_type_floatOfRawIntOp : conv

topval reduce_res_type_rawIntOfIntOp : conv
topval reduce_arg1_type_rawIntOfIntOp : conv

topval reduce_res_type_rawIntOfEnumOp : conv
topval reduce_arg1_type_rawIntOfEnumOp : conv

topval reduce_res_type_rawIntOfFloatOp : conv
topval reduce_arg1_type_rawIntOfFloatOp : conv

topval reduce_res_type_rawIntOfRawIntOp : conv
topval reduce_arg1_type_rawIntOfRawIntOp : conv

topval reduce_res_type_dtupleOfDTupleOp : conv
topval reduce_arg1_type_dtupleOfDTupleOp : conv

topval reduce_res_type_unionOfUnionOp : conv
topval reduce_arg1_type_unionOfUnionOp : conv

topval reduce_res_type_rawDataOfFrameOp : conv
topval reduce_arg1_type_rawDataOfFrameOp : conv

topval reduce_res_type_andEnumOp : conv
topval reduce_arg1_type_andEnumOp : conv
topval reduce_arg2_type_andEnumOp : conv

topval reduce_res_type_orEnumOp : conv
topval reduce_arg1_type_orEnumOp : conv
topval reduce_arg2_type_orEnumOp : conv

topval reduce_res_type_xorEnumOp : conv
topval reduce_arg1_type_xorEnumOp : conv
topval reduce_arg2_type_xorEnumOp : conv

topval reduce_res_type_plusIntOp : conv
topval reduce_arg1_type_plusIntOp : conv
topval reduce_arg2_type_plusIntOp : conv

topval reduce_res_type_minusIntOp : conv
topval reduce_arg1_type_minusIntOp : conv
topval reduce_arg2_type_minusIntOp : conv

topval reduce_res_type_mulIntOp : conv
topval reduce_arg1_type_mulIntOp : conv
topval reduce_arg2_type_mulIntOp : conv

topval reduce_res_type_divIntOp : conv
topval reduce_arg1_type_divIntOp : conv
topval reduce_arg2_type_divIntOp : conv

topval reduce_res_type_remIntOp : conv
topval reduce_arg1_type_remIntOp : conv
topval reduce_arg2_type_remIntOp : conv

topval reduce_res_type_lslIntOp : conv
topval reduce_arg1_type_lslIntOp : conv
topval reduce_arg2_type_lslIntOp : conv

topval reduce_res_type_lsrIntOp : conv
topval reduce_arg1_type_lsrIntOp : conv
topval reduce_arg2_type_lsrIntOp : conv

topval reduce_res_type_asrIntOp : conv
topval reduce_arg1_type_asrIntOp : conv
topval reduce_arg2_type_asrIntOp : conv

topval reduce_res_type_andIntOp : conv
topval reduce_arg1_type_andIntOp : conv
topval reduce_arg2_type_andIntOp : conv

topval reduce_res_type_orIntOp : conv
topval reduce_arg1_type_orIntOp : conv
topval reduce_arg2_type_orIntOp : conv

topval reduce_res_type_xorIntOp : conv
topval reduce_arg1_type_xorIntOp : conv
topval reduce_arg2_type_xorIntOp : conv

topval reduce_res_type_maxIntOp : conv
topval reduce_arg1_type_maxIntOp : conv
topval reduce_arg2_type_maxIntOp : conv

topval reduce_res_type_eqIntOp : conv
topval reduce_arg1_type_eqIntOp : conv
topval reduce_arg2_type_eqIntOp : conv

topval reduce_res_type_neqIntOp : conv
topval reduce_arg1_type_neqIntOp : conv
topval reduce_arg2_type_neqIntOp : conv

topval reduce_res_type_ltIntOp : conv
topval reduce_arg1_type_ltIntOp : conv
topval reduce_arg2_type_ltIntOp : conv

topval reduce_res_type_leIntOp : conv
topval reduce_arg1_type_leIntOp : conv
topval reduce_arg2_type_leIntOp : conv

topval reduce_res_type_gtIntOp : conv
topval reduce_arg1_type_gtIntOp : conv
topval reduce_arg2_type_gtIntOp : conv

topval reduce_res_type_geIntOp : conv
topval reduce_arg1_type_geIntOp : conv
topval reduce_arg2_type_geIntOp : conv

topval reduce_res_type_cmpIntOp : conv
topval reduce_arg1_type_cmpIntOp : conv
topval reduce_arg2_type_cmpIntOp : conv

topval reduce_res_type_plusRawIntOp : conv
topval reduce_arg1_type_plusRawIntOp : conv
topval reduce_arg2_type_plusRawIntOp : conv

topval reduce_res_type_minusRawIntOp : conv
topval reduce_arg1_type_minusRawIntOp : conv
topval reduce_arg2_type_minusRawIntOp : conv

topval reduce_res_type_mulRawIntOp : conv
topval reduce_arg1_type_mulRawIntOp : conv
topval reduce_arg2_type_mulRawIntOp : conv

topval reduce_res_type_divRawIntOp : conv
topval reduce_arg1_type_divRawIntOp : conv
topval reduce_arg2_type_divRawIntOp : conv

topval reduce_res_type_remRawIntOp : conv
topval reduce_arg1_type_remRawIntOp : conv
topval reduce_arg2_type_remRawIntOp : conv

topval reduce_res_type_slRawIntOp : conv
topval reduce_arg1_type_slRawIntOp : conv
topval reduce_arg2_type_slRawIntOp : conv

topval reduce_res_type_srRawIntOp : conv
topval reduce_arg1_type_srRawIntOp : conv
topval reduce_arg2_type_srRawIntOp : conv

topval reduce_res_type_andRawIntOp : conv
topval reduce_arg1_type_andRawIntOp : conv
topval reduce_arg2_type_andRawIntOp : conv

topval reduce_res_type_orRawIntOp : conv
topval reduce_arg1_type_orRawIntOp : conv
topval reduce_arg2_type_orRawIntOp : conv

topval reduce_res_type_xorRawIntOp : conv
topval reduce_arg1_type_xorRawIntOp : conv
topval reduce_arg2_type_xorRawIntOp : conv

topval reduce_res_type_maxRawIntOp : conv
topval reduce_arg1_type_maxRawIntOp : conv
topval reduce_arg2_type_maxRawIntOp : conv

topval reduce_res_type_minRawIntOp : conv
topval reduce_arg1_type_minRawIntOp : conv
topval reduce_arg2_type_minRawIntOp : conv

topval reduce_res_type_eqRawIntOp : conv
topval reduce_arg1_type_eqRawIntOp : conv
topval reduce_arg2_type_eqRawIntOp : conv

topval reduce_res_type_neqRawIntOp : conv
topval reduce_arg1_type_neqRawIntOp : conv
topval reduce_arg2_type_neqRawIntOp : conv

topval reduce_res_type_ltRawIntOp : conv
topval reduce_arg1_type_ltRawIntOp : conv
topval reduce_arg2_type_ltRawIntOp : conv

topval reduce_res_type_leRawIntOp : conv
topval reduce_arg1_type_leRawIntOp : conv
topval reduce_arg2_type_leRawIntOp : conv

topval reduce_res_type_gtRawIntOp : conv
topval reduce_arg1_type_gtRawIntOp : conv
topval reduce_arg2_type_gtRawIntOp : conv

topval reduce_res_type_geRawIntO : conv
topval reduce_arg1_type_geRawIntO : conv
topval reduce_arg2_type_geRawIntO : conv

topval reduce_res_type_cmpRawIntOp : conv
topval reduce_arg1_type_cmpRawIntOp : conv
topval reduce_arg2_type_cmpRawIntOp : conv

topval reduce_res_type_plusFloatOp : conv
topval reduce_arg1_type_plusFloatOp : conv
topval reduce_arg2_type_plusFloatOp : conv

topval reduce_res_type_minusFloatOp : conv
topval reduce_arg1_type_minusFloatOp : conv
topval reduce_arg2_type_minusFloatOp : conv

topval reduce_res_type_mulFloatOp : conv
topval reduce_arg1_type_mulFloatOp : conv
topval reduce_arg2_type_mulFloatOp : conv

topval reduce_res_type_divFloatOp : conv
topval reduce_arg1_type_divFloatOp : conv
topval reduce_arg2_type_divFloatOp : conv

topval reduce_res_type_remFloatOp : conv
topval reduce_arg1_type_remFloatOp : conv
topval reduce_arg2_type_remFloatOp : conv

topval reduce_res_type_maxFloatOp : conv
topval reduce_arg1_type_maxFloatOp : conv
topval reduce_arg2_type_maxFloatOp : conv

topval reduce_res_type_minFloatOp : conv
topval reduce_arg1_type_minFloatOp : conv
topval reduce_arg2_type_minFloatOp : conv

topval reduce_res_type_eqFloatOp : conv
topval reduce_arg1_type_eqFloatOp : conv
topval reduce_arg2_type_eqFloatOp : conv

topval reduce_res_type_neqFloatOp : conv
topval reduce_arg1_type_neqFloatOp : conv
topval reduce_arg2_type_neqFloatOp : conv

topval reduce_res_type_ltFloatOp : conv
topval reduce_arg1_type_ltFloatOp : conv
topval reduce_arg2_type_ltFloatOp : conv

topval reduce_res_type_leFloatOp : conv
topval reduce_arg1_type_leFloatOp : conv
topval reduce_arg2_type_leFloatOp : conv

topval reduce_res_type_gtFloatOp : conv
topval reduce_arg1_type_gtFloatOp : conv
topval reduce_arg2_type_gtFloatOp : conv

topval reduce_res_type_geFloatOp : conv
topval reduce_arg1_type_geFloatOp : conv
topval reduce_arg2_type_geFloatOp : conv

topval reduce_res_type_cmpFloatOp : conv
topval reduce_arg1_type_cmpFloatOp : conv
topval reduce_arg2_type_cmpFloatOp : conv

topval reduce_res_type_atan2FloatOp : conv
topval reduce_arg1_type_atan2FloatOp : conv
topval reduce_arg2_type_atan2FloatOp : conv

topval reduce_res_type_powerFloatOp : conv
topval reduce_arg1_type_powerFloatOp : conv
topval reduce_arg2_type_powerFloatOp : conv

topval reduce_res_type_ldExpFloatIntOp : conv
topval reduce_arg1_type_ldExpFloatIntOp : conv
topval reduce_arg2_type_ldExpFloatIntOp : conv

topval reduce_res_type_eqEqOp : conv
topval reduce_arg1_type_eqEqOp : conv
topval reduce_arg2_type_eqEqOp : conv

topval reduce_res_type_neqEqOp : conv
topval reduce_arg1_type_neqEqOp : conv
topval reduce_arg2_type_neqEqOp : conv