(*
 * Finite sets.
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
 * Copyright (C) 1998 Jason Hickey, Cornell University
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
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *
 *)

extends Itt_bool
extends Itt_fun
extends Itt_quotient
extends Itt_list
extends Itt_list2

open Basic_tactics

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare fset{'eq; 'T}
declare feset{'eq; 'T}
declare fempty
declare fsingleton{'x}
declare funion{'eq; 's1; 's2}
declare fisect{'eq; 's1; 's2}
declare fsub{'eq; 's1; 's2}

declare fisempty{'s}
declare fmember{'eq; 'x; 's1}
declare fsubseteq{'eq; 's1; 's2}
declare fequal{'eq; 's1; 's2}

declare fequalp{'eq; 'T}
declare fsquash{'eq; 's}

declare fball{'s; x. 'b['x]}
declare fbexists{'s; x. 'b['x]}
declare fall{'eq; 'T; 's; x. 'b['x]}
declare fexists{'eq; 'T; 's; x. 'b['x]}

declare foflist{'l}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

topval unfold_fcompare : conv
topval unfold_fequalp : conv
topval unfold_fset : conv
topval unfold_fempty : conv
topval unfold_fsingleton : conv
topval unfold_funion : conv
topval unfold_fisect : conv
topval unfold_fsub : conv
topval unfold_fmember : conv
topval unfold_fisempty : conv
topval unfold_fsubseteq : conv
topval unfold_fequal : conv
topval unfold_fsquash : conv
topval unfold_fball : conv
topval unfold_fbexists : conv
topval unfold_feset : conv
topval unfold_fall : conv
topval unfold_fexists : conv
topval unfold_foflist : conv

topval fold_fequalp : conv
topval fold_fset : conv
topval fold_fempty : conv
topval fold_fsingleton : conv
topval fold_fisect : conv
topval fold_fsub : conv
topval fold_fmember : conv
topval fold_fisempty : conv
topval fold_fsubseteq : conv
topval fold_fequal : conv
topval fold_fsquash : conv
topval fold_fball : conv
topval fold_fbexists : conv
topval fold_feset : conv
topval fold_fall : conv
topval fold_fexists : conv
topval fold_foflist : conv

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval fmember_subst_elementT : term -> tactic
topval fcompareSymT : tactic
topval fcompareTransT : term -> tactic
topval fsubseteqTransT : term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "mp.run"
 * End:
 * -*-
 *)
