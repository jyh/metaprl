(*
 * Polynomials.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
 *
 * Copyright (C) 1997-2004 MetaPRL Group
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
 * Author: Xin Yu
 * Email : xiny@cs.caltech.edu
 *)

extends Itt_cyclic_group

open Tactic_type.Tactic

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare poly{'f}
declare zero_poly{'f}
declare unit_poly{'f}
declare isZero{'a; 'f}
declare isZeroPoly{'p; 'f}
declare deg{'p}
declare coeff{'p; 'i; 'f}
declare normalize{'p; 'f}
declare add_const{'p; 'a; 'f}
declare mul_const{'p; 'a; 'f}
declare add_poly{'p; 'q; 'f}
declare neg_poly{'p; 'f}
declare sum{'i; 'j; x.'P['x]; 'f}
declare mul_poly{'p; 'q; 'f}
declare eval_poly{'p; 'a; 'f}
declare eq_poly{'p; 'q; 'f}

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval unfold_poly : conv
topval unfold_zero_poly : conv
topval unfold_unit_poly : conv
topval unfold_isZero : conv
topval unfold_isZeroPoly : conv
topval unfold_deg : conv
topval unfold_coeff : conv
topval unfold_normalize : conv
topval unfold_normalize1 : conv
topval unfold_add_const : conv
topval unfold_mul_const : conv
topval unfold_add_poly : conv
topval unfold_neg_poly : conv
topval unfold_sum: conv
topval unfold_mul_poly : conv
topval unfold_eval_poly : conv
topval unfold_eval_poly1 : conv
topval unfold_eq_poly : conv

topval fold_poly : conv
topval fold_zero_poly : conv
topval fold_unit_poly : conv
topval fold_isZero : conv
topval fold_isZeroPoly : conv
topval fold_deg : conv
topval fold_coeff : conv
topval fold_normalize : conv
topval fold_normalize1 : conv
topval fold_add_const : conv
topval fold_mul_const : conv
topval fold_add_poly : conv
topval fold_neg_poly : conv
(*topval fold_sum: conv*)
topval fold_mul_poly : conv
topval fold_eval_poly : conv
topval fold_eval_poly1 : conv
topval fold_eq_poly : conv

topval coeffZeropolyC : conv
topval coeffZeropoly1C : conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
