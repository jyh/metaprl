(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Fold constants together in FIR expressions.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
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
 * Email:  emre@its.caltech.edu
 *)

include Fir_ty
include Fir_exp
include Mp_mc_fir_eval

open Mp_mc_fir_eval
open Top_conversionals

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(*
 * I'm assuming well formed expressions here.
 * If that isn't the case, things will fall apart later on...
 *)

interactive_rw const_elim_atomVar_Int :
   atomVar{ atomInt{'i} } <--> atomInt{'i}

interactive_rw const_elim_atomVar_RawInt :
   atomVar{ atomRawInt{'p; 's; 'i} } <--> atomRawInt{'p; 's; 'i}

interactive_rw const_elim_atomInt :
   letBinop{ 'op; tyInt; atomInt{'a1}; atomInt{'a2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ 'op; tyInt; 'a1; 'a2 } ]

interactive_rw const_elim_atomRawInt :
   letBinop{ 'op; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v.'exp['v] } <-->
   'exp[ binop_exp{ 'op; tyRawInt{'p; 's}; 'a1; 'a2 } ]

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
      reduce_mod_arith;
      reduce_mod_arith_signed;
      reduce_mod_arith_unsigned;

      reduce_val_true;
      reduce_val_false;
      reduce_atomEnum_eq_atom;

      reduce_beta;

      reduce_plusIntOp;
      reduce_minusIntOp;
      reduce_mulIntOp;
      reduce_divIntOp;
      reduce_remIntOp;
      reduce_maxIntOp;
      reduce_minIntOp;
      reduce_eqIntOp;
      reduce_neqIntOp;
      reduce_ltIntOp;
      reduce_leIntOp;
      reduce_gtIntOp;
      reduce_geIntOp;
      reduce_cmpIntOp;

      reduce_plusRawIntOp;
      reduce_minusRawIntOp;
      reduce_mulRawIntOp;
      reduce_divRawIntOp;
      reduce_remRawIntOp;
      reduce_maxRawIntOp;
      reduce_minRawIntOp;
      reduce_eqRawIntOp;
      reduce_neqRawIntOp;
      reduce_ltRawIntOp;
      reduce_leRawIntOp;
      reduce_gtRawIntOp;
      reduce_geRawIntOp;
      reduce_cmpRawIntOp;

      (* Now we get to the rewrites we defined above. *)

      const_elim_atomVar_Int;
      const_elim_atomVar_RawInt;
      const_elim_atomInt;
      const_elim_atomRawInt;

      (* Clean up anything else that remains. *)

      reduceTopC
   ] )) i
