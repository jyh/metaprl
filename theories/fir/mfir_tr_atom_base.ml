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
 * I need to put some documentation here eventually.
 * @end[doc]
 *)

declare res_type{ 'op }
declare arg1_type{ 'op }
declare arg2_type{ 'op }


(**************************************************************************
 * Rewrites.
 **************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * Maybe I should put some documentation here.
 * @end[doc]
 *)

(*!
 * @docoff
 *)

prim_rw reduce_res_type_notEnumOp :
   res_type{ notEnumOp[i:n] } <-->
   tyEnum[i:n]

prim_rw reduce_res_type_uminusIntOp :
   res_type{ uminusIntOp } <-->
   tyInt

prim_rw reduce_res_type_notIntOp :
   res_type{ notIntOp } <-->
   tyInt

prim_rw reduce_res_type_absIntOp :
   res_type{ absIntOp } <-->
   tyInt


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
