(*
 * Polynomials.
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

extends Itt_field2

open Tactic_type.Conversionals

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare eqDecidable{'f}

declare prefieldE[i:l]
declare isFieldE{'f}
declare fieldE[i:l]

declare poly{'f}
declare zero_poly{'f}
declare isZero{'a; 'f}
declare isZeroPoly{'p; 'f}
declare deg{'p}
declare coeff{'p; 'i; 'f}
declare normalize{'p; 'f}
declare add_const{'p; 'a; 'f}
declare mul_const{'p; 'a; 'f}
declare add{'p; 'q; 'f}
declare sum{'i; 'j; x.'P['x]; 'f}
declare mul{'p; 'q; 'f}
declare eval_poly{'p; 'a; 'f}

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval unfold_eqDecidable : conv
topval fold_eqDecidable : conv

topval unfold_prefieldE : conv
topval unfold_isFieldE : conv
topval unfold_fieldE : conv

topval fold_prefieldE1 : conv
topval fold_prefieldE : conv
topval fold_isFieldE1 : conv
topval fold_isFieldE : conv
topval fold_fieldE1 : conv
topval fold_fieldE : conv

topval unfold_poly : conv
topval unfold_zero_poly : conv
topval unfold_isZero : conv
topval unfold_isZeroPoly : conv
topval unfold_deg : conv
topval unfold_coeff : conv
topval unfold_normalize : conv
topval unfold_add_const : conv
topval unfold_mul_const : conv
topval unfold_add : conv
topval unfold_sum : conv
topval unfold_mul : conv
topval unfold_eval_poly : conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)