(*!
 * @begin[doc]
 * @theory[Mp_mc_const_elim]
 *
 * The @tt{Mp_mc_const_elim} module provides rewrites to perform
 * constant elimination (folding) in FIR programs.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
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
 * @email{emre@its.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Mp_mc_fir_ty
include Mp_mc_fir_exp
include Mp_mc_fir_eval
(*! @docoff *)

open Mp_mc_fir_eval
open Top_conversionals

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(*
 * Unary operations.
 *)

interactive_rw const_elim_uminusIntOp :
   letUnop{ tyInt; uminusIntOp; atomInt{ 'int }; var. 'exp['var] } <-->
   'exp[ unop_exp{ uminusIntOp; tyInt; 'int} ]

interactive_rw const_elim_uminusRawIntOp :
   letUnop{ tyRawInt{'p; 's}; uminusRawIntOp{'p; 's};
            atomRawInt{'p; 's; 'num}; var. 'exp['var] } <-->
   'exp[ unop_exp{ uminusRawIntOp{'p; 's}; tyRawInt{'p; 's}; 'num } ]

(*
 * Binary operations.
 *)

(* Naml ints. *)

interactive_rw const_elim_plusIntOp :
   letBinop{ tyInt; plusIntOp; atomInt{'i1}; atomInt{'i2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ plusIntOp; tyInt; 'i1; 'i2 } ]

interactive_rw const_elim_minusIntOp :
   letBinop{ tyInt; minusIntOp; atomInt{'i1}; atomInt{'i2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ minusIntOp; tyInt; 'i1; 'i2 } ]

interactive_rw const_elim_mulIntOp :
   letBinop{ tyInt; mulIntOp; atomInt{'i1}; atomInt{'i2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ mulIntOp; tyInt; 'i1; 'i2 } ]

(* Native ints. *)

interactive_rw const_elim_plusRawIntOp :
   letBinop{ tyRawInt{'p; 's}; plusRawIntOp{'p; 's};
      atomRawInt{'p; 's; 'i1}; atomRawInt{'p; 's; 'i2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ plusRawIntOp{'p; 's}; tyRawInt{'p; 's}; 'i1; 'i2 } ]

interactive_rw const_elim_minusRawIntOp :
   letBinop{ tyRawInt{'p; 's}; minusRawIntOp{'p; 's};
      atomRawInt{'p; 's; 'i1}; atomRawInt{'p; 's; 'i2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ minusRawIntOp{'p; 's}; tyRawInt{'p; 's}; 'i1; 'i2 } ]

interactive_rw const_elim_mulRawIntOp :
   letBinop{ tyRawInt{'p; 's}; mulRawIntOp{'p; 's};
      atomRawInt{'p; 's; 'i1}; atomRawInt{'p; 's; 'i2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ mulRawIntOp{'p; 's}; tyRawInt{'p; 's}; 'i1; 'i2 } ]

(*
 * Normal values.
 *)

interactive_rw const_elim_atomVar_atomInt :
   atomVar{ atomInt{'i} } <--> atomInt{'i}

interactive_rw const_elim_atomVar_atomRawInt :
   atomVar{ atomRawInt{'p; 's; 'i} } <--> atomRawInt{'p; 's; 'i}

(*************************************************************************
 * Automation
 *************************************************************************)

let firConstElimT i =
   rwh (repeatC (applyAllC [

      (* Many other rewrites are needed to support this optimization. *)

      reduce_naml_prec;
      reduce_int8;
      reduce_int16;
      reduce_int32;
      reduce_int64;
      reduce_pow_2_7;
      reduce_pow_2_8;
      reduce_pow_2_15;
      reduce_pow_2_16;
      reduce_pow_2_30;
      reduce_pow_2_31;
      reduce_pow_2_32;
      reduce_pow_2_63;
      reduce_pow_2_64;
      reduce_pow;
      reduce_mod_arith1;
      reduce_mod_arith2;
      reduce_mod_arith_signed;
      reduce_mod_arith_unsigned;

      reduce_plusIntOp;
      reduce_minusIntOp;
      reduce_mulIntOp;
      reduce_divIntOp;
      reduce_remIntOp;
      reduce_maxIntOp;
      reduce_minIntOp;

      reduce_plusRawIntOp;
      reduce_minusRawIntOp;
      reduce_mulRawIntOp;
      reduce_divRawIntOp;
      reduce_remRawIntOp;
      reduce_maxRawIntOp;
      reduce_minRawIntOp;

      (* Now we include the rewrites we defined above. *)

      const_elim_uminusIntOp;
      const_elim_uminusRawIntOp;

      const_elim_plusIntOp;
      const_elim_minusIntOp;
      const_elim_mulIntOp;

      const_elim_plusRawIntOp;
      const_elim_minusRawIntOp;
      const_elim_mulRawIntOp;

      const_elim_atomVar_atomInt;
      const_elim_atomVar_atomRawInt;

      (* Clean up anything else that remains. *)

      reduceTopC
   ] )) i
