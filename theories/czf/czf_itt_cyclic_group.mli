(*
 * Cyclic group.
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
 * Copyright (C) 2002 Xin Yu, Caltech
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

extends Czf_itt_group
extends Czf_itt_cyclic_subgroup

open Tactic_type.Tactic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare cycg{'g}
declare cycgroup{'g; 'a}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

rewrite unfold_cycg : cycg{'g} <-->
   (group{'g} & (exst a: set. (mem{'a; car{'g}} & all x: set. (mem{'x; car{'g}} => (exst n: int. eq{'x; power{'g; 'a; 'n}})))))

rewrite unfold_cycgroup : cycgroup{'g; 'a} <-->
   (group{'g} & mem{'a; car{'g}} & equal{car{'g}; sep{car{'g}; x. (exst n: int. eq{'x; power{'g; 'a; 'n}})}})

topval fold_cycgroup : conv

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Every cyclic group is abelian.
 *)
topval cycgAbelT: tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
