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
   'exp[ atomInt{ mod_arith{ naml_prec; val_true; ('i +@ 'j) } } ]
interactive_rw const_elim_minusIntOp :
   letBinop{ minusIntOp; tyInt; atomInt{'i}; atomInt{'j};  v. 'exp['v] } <-->
   'exp[ atomInt{ mod_arith{ naml_prec; val_true; ('i -@ 'j) } } ]
interactive_rw const_elim_mulIntOp :
   letBinop{ mulIntOp; tyInt; atomInt{'i}; atomInt{'j}; v. 'exp['v] } <-->
   'exp[ atomInt{ mod_arith{ naml_prec; val_true; ('i *@ 'j) } } ]
interactive_rw const_elim_divIntOp :
   letBinop{ divIntOp; tyInt; atomInt{'i}; atomInt{'j}; v. 'exp['v] } <-->
   'exp[ atomInt{ mod_arith{ naml_prec; val_true; ('i /@ 'j) } } ]
interactive_rw const_elim_remIntOp :
   letBinop{ remIntOp; tyInt; atomInt{'i}; atomInt{'j}; v. 'exp['v] } <-->
   'exp[ atomInt{ mod_arith{ naml_prec; val_true; ('i %@ 'j) } } ]

(*
 * Native integers.
 *)

interactive_rw const_elim_plusRawIntOp :
   letBinop{ plusRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ atomRawInt{'p; 's; mod_arith{'p; 's; ('a1 +@ 'a2)} } ]
interactive_rw const_elim_minusRawIntOp :
   letBinop{ minusRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ atomRawInt{'p; 's; mod_arith{'p; 's; ('a1 -@ 'a2)} } ]
interactive_rw const_elim_mulRawIntOp :
   letBinop{ mulRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ atomRawInt{'p; 's; mod_arith{'p; 's; ('a1 *@ 'a2)} } ]
interactive_rw const_elim_divRawIntOp :
   letBinop{ divRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ atomRawInt{'p; 's; mod_arith{'p; 's; ('a1 /@ 'a2)} } ]
interactive_rw const_elim_remRawIntOp :
   letBinop{ remRawIntOp{'p; 's}; tyRawInt{'p; 's};
      atomRawInt{'p; 's; 'a1}; atomRawInt{'p; 's; 'a2}; v. 'exp['v] } <-->
   'exp[ atomRawInt{'p; 's; mod_arith{'p; 's; ('a1 %@ 'a2)} } ]

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

      reduce_beta;

      (* Now we get to the rewrites we defined above. *)

      const_elim_plusIntOp;
      const_elim_minusIntOp;
      const_elim_mulIntOp;
      const_elim_divIntOp;
      const_elim_remIntOp;

      const_elim_plusRawIntOp;
      const_elim_minusRawIntOp;
      const_elim_mulRawIntOp;
      const_elim_divRawIntOp;
      const_elim_remRawIntOp;

      reduceTopC
   ] )) i
