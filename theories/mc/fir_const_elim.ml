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

include Fir_int_set
include Fir_ty
include Fir_exp
include Fir_eval

open Fir_eval
open Top_conversionals
open Tactic_type.Conversionals

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(*
 * I'm assuming well formed atom(Raw)Int's here.
 * The results should be kept in atom(Raw)Int's to preserve the
 * structure of the FIR.
 *)

(*
 * Naml integers.
 *)

interactive_rw const_elim_plusIntOp :
   letBinop{ plusIntOp; tyInt; atomInt{'i}; atomInt{'j}; v. 'exp['v] } <-->
   'exp[ binop_exp{ plusIntOp; tyInt; 'i; 'j } ]
interactive_rw const_elim_minusIntOp :
   letBinop{ minusIntOp; tyInt; atomInt{'i}; atomInt{'j};  v. 'exp['v] } <-->
   'exp[ binop_exp{ minusIntOp; tyInt; 'i; 'j } ]
interactive_rw const_elim_mulIntOp :
   letBinop{ mulIntOp; tyInt; atomInt{'i}; atomInt{'j}; v. 'exp['v] } <-->
   'exp[ binop_exp{ mulIntOp; tyInt; 'i; 'j } ]
interactive_rw const_elim_divIntOp :
   letBinop{ divIntOp; tyInt; atomInt{'i}; atomInt{'j}; v. 'exp['v] } <-->
   'exp[ binop_exp{ divIntOp; tyInt; 'i; 'j } ]
interactive_rw const_elim_remIntOp :
   letBinop{ remIntOp; tyInt; atomInt{'i}; atomInt{'j}; v. 'exp['v] } <-->
   'exp[ binop_exp{ remIntOp; tyInt; 'i; 'j } ]

interactive_rw const_elim_maxIntOp :
   letBinop{ maxIntOp; tyInt; atomInt{'i}; atomInt{'j}; v. 'exp['v] } <-->
   'exp[ binop_exp{ maxIntOp; tyInt; 'i; 'j } ]
interactive_rw const_elim_minIntOp :
   letBinop{ minIntOp; tyInt; atomInt{'i}; atomInt{'j}; v. 'exp['v] } <-->
   'exp[ binop_exp{ minIntOp; tyInt; 'i; 'j } ]

interactive_rw const_elim_eqIntOp :
   letBinop{ eqIntOp; tyEnum{ 2 };
      atomInt{'i}; atomInt{'j}; v. 'exp['v] } <-->
   'exp[ binop_exp{ eqIntOp; tyEnum{2}; 'i; 'j } ]
interactive_rw const_elim_neqIntOp :
   letBinop{ neqIntOp; tyEnum{ 2 };
      atomInt{'i}; atomInt{'j}; v. 'exp['v] } <-->
   'exp[ binop_exp{ neqIntOp; tyEnum{2}; 'i; 'j } ]
interactive_rw const_elim_ltIntOp :
   letBinop{ ltIntOp; tyEnum{ 2 };
      atomInt{'i}; atomInt{'j}; v. 'exp['v] } <-->
   'exp[ binop_exp{ ltIntOp; tyEnum{2}; 'i; 'j } ]
interactive_rw const_elim_leIntOp :
   letBinop{ leIntOp; tyEnum{ 2 };
      atomInt{'i}; atomInt{'j}; v. 'exp['v] } <-->
   'exp[ binop_exp{ leIntOp; tyEnum{2}; 'i; 'j } ]
interactive_rw const_elim_gtIntOp :
   letBinop{ gtIntOp; tyEnum{ 2 };
      atomInt{'i}; atomInt{'j}; v. 'exp['v] } <-->
   'exp[ binop_exp{ gtIntOp; tyEnum{2}; 'i; 'j } ]
interactive_rw const_elim_geIntOp :
   letBinop{ geIntOp; tyEnum{ 2 };
      atomInt{'i}; atomInt{'j}; v. 'exp['v] } <-->
   'exp[ binop_exp{ geIntOp; tyEnum{2}; 'i; 'j } ]
interactive_rw const_elim_cmpIntOp :
   letBinop{ cmpIntOp; tyEnum{ 2 };
      atomInt{'i}; atomInt{'j}; v. 'exp['v] } <-->
   'exp[ binop_exp{ cmpIntOp; tyEnum{2}; 'i; 'j } ]

(*
 * Native integers.
 *)

interactive_rw const_elim_plusRawIntOp :
   letBinop{ plusRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ plusRawIntOp{'p;'s}; tyRawInt{'p;'s}; 'a1; 'a2 } ]
interactive_rw const_elim_minusRawIntOp :
   letBinop{ minusRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ minusRawIntOp{'p;'s}; tyRawInt{'p;'s}; 'a1; 'a2 } ]
interactive_rw const_elim_mulRawIntOp :
   letBinop{ mulRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ mulRawIntOp{'p;'s}; tyRawInt{'p;'s}; 'a1; 'a2 } ]
interactive_rw const_elim_divRawIntOp :
   letBinop{ divRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ divRawIntOp{'p;'s}; tyRawInt{'p;'s}; 'a1; 'a2 } ]
interactive_rw const_elim_remRawIntOp :
   letBinop{ remRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ remRawIntOp{'p;'s}; tyRawInt{'p;'s}; 'a1; 'a2 } ]

interactive_rw const_elim_maxRawIntOp :
   letBinop{ maxRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ maxRawIntOp{'p;'s}; tyRawInt{'p;'s}; 'a1; 'a2 } ]
interactive_rw const_elim_minRawIntOp :
   letBinop{ minRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ minRawIntOp{'p;'s}; tyRawInt{'p;'s}; 'a1; 'a2 } ]

interactive_rw const_elim_eqRawIntOp :
   letBinop{ eqRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ eqRawIntOp{'p;'s}; tyRawInt{'p;'s}; 'a1; 'a2 } ]
interactive_rw const_elim_neqRawIntOp :
   letBinop{ neqRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ neqRawIntOp{'p;'s}; tyRawInt{'p;'s}; 'a1; 'a2 } ]
interactive_rw const_elim_ltRawIntOp :
   letBinop{ ltRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ ltRawIntOp{'p;'s}; tyRawInt{'p;'s}; 'a1; 'a2 } ]
interactive_rw const_elim_leRawIntOp :
   letBinop{ leRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ leRawIntOp{'p;'s}; tyRawInt{'p;'s}; 'a1; 'a2 } ]
interactive_rw const_elim_gtRawIntOp :
   letBinop{ gtRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ gtRawIntOp{'p;'s}; tyRawInt{'p;'s}; 'a1; 'a2 } ]
interactive_rw const_elim_geRawIntOp :
   letBinop{ geRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ geRawIntOp{'p;'s}; tyRawInt{'p;'s}; 'a1; 'a2 } ]
interactive_rw const_elim_cmpRawIntOp :
   letBinop{ cmpRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ binop_exp{ cmpRawIntOp{'p;'s}; tyRawInt{'p;'s}; 'a1; 'a2 } ]

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
      reduce_pow_2_8;
      reduce_pow_2_16;
      reduce_pow_2_31;
      reduce_pow_2_32;
      reduce_pow_2_64;
      reduce_pow;
      reduce_mod_arith;
      reduce_mod_arith_signed;
      reduce_mod_arith_unsigned;

      reduce_val_true;
      reduce_val_false;
      reduce_atomEnum_eq;

      reduce_beta;

      (* Now we get to the rewrites we defined above. *)

      const_elim_plusIntOp;
      const_elim_minusIntOp;
      const_elim_mulIntOp;
      const_elim_divIntOp;
      const_elim_remIntOp;
      const_elim_maxIntOp;
      const_elim_minIntOp;
      const_elim_eqIntOp;
      const_elim_neqIntOp;
      const_elim_ltIntOp;
      const_elim_leIntOp;
      const_elim_gtIntOp;
      const_elim_geIntOp;
      const_elim_cmpIntOp;

      const_elim_plusRawIntOp;
      const_elim_minusRawIntOp;
      const_elim_mulRawIntOp;
      const_elim_divRawIntOp;
      const_elim_remRawIntOp;
      const_elim_maxRawIntOp;
      const_elim_minRawIntOp;
      const_elim_eqRawIntOp;
      const_elim_neqRawIntOp;
      const_elim_ltRawIntOp;
      const_elim_leRawIntOp;
      const_elim_gtRawIntOp;
      const_elim_geRawIntOp;
      const_elim_cmpRawIntOp;

      reduceTopC
   ] )) i
