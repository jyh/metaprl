(*
 * More structural rules.
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
 * Copyright (C) 2001-2005 MetaPRL Group, Cornell University
 * and California Institute of Technology
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
 *)

extends Itt_struct
extends Itt_sqsimple

open Basic_tactics

topval letT : term -> tactic
topval genT : term -> tactic

topval assertEqT  : term -> tactic

topval assertSquashT  : term -> tactic
topval assertSquashAtT  : int -> term -> tactic

topval genSOVarT : string -> tactic

topval foldCloseC : string list -> term -> conv
topval foldApplyC : term -> conv

topval lambdaSqElim1T : int -> term -> tactic
topval lambdaSqElim2T : int -> term -> tactic
topval lambdaSqElimFull2T : int -> term -> term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
