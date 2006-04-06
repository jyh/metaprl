(*
 * Squiggle equality.
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
 * Copyright (C) 2001-2006 MetaPRL Group, Cornell University and
 * California Institute of Technology
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
 * Author: Alexei Kopylov <kopylov@cs.cornell.edu>
 * Modified by: Aleksey Nogin <nogin@cs.caltech.edu>
 *              Jason Hickey <jyh@cs.caltech.edu>
 *)
extends Itt_equal
extends Itt_struct

open Basic_tactics

val squiggle_term : term
val is_squiggle_term : term -> bool
val dest_squiggle : term -> term * term
val mk_squiggle_term : term -> term -> term

val squiggle_memberEquality : tactic

val sq_subst_forward : int -> int -> term -> tactic
val sq_subst_backward : int -> int -> term -> tactic

topval sqSubstT : term -> int -> tactic
topval sqSymT : tactic

topval hypC : int -> conv
topval revHypC : int -> conv
topval assumC : int -> conv
topval revAssumC : int -> conv

(* Helper function for sq_subst_forward/sq_subst_backward tactics *)
val least_fw_index : SeqHyp.t -> SymbolSet.t -> SymbolSet.t -> int -> bool * int

(************************************************************************
 * Grammar.
 *)
production xterm_term{'e1 ~ 'e2} <--
   xterm_term{'e1}; tok_tilde; xterm_term{'e2}

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
