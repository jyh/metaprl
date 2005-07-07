(*
 * Rings.
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

extends Itt_group
extends Itt_record_renaming

open Tactic_type.Tactic

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare isRDistrib{'r}
declare isLDistrib{'r}
declare isDistrib{'r}

declare prering[i:l]
declare isRing{'G}
declare ring[i:l]

declare Z
declare Zeven

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_add
prec prec_neg

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval unfold_isRDistrib : conv
topval unfold_isLDistrib : conv
topval unfold_isDistrib : conv
topval fold_isRDistrib : conv
topval fold_isLDistrib : conv
topval fold_isDistrib : conv

topval unfold_prering : conv
topval unfold_isRing : conv
topval unfold_ring : conv

topval fold_prering : conv
topval fold_isRing1 : conv
topval fold_isRing : conv
topval fold_ring1 : conv
topval fold_ring : conv

topval unfold_Z : conv
topval unfold_Zeven : conv
topval fold_Z : conv
topval fold_Z_car : conv
topval fold_Zeven : conv

topval unfold_subring : conv
topval fold_subring : conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
