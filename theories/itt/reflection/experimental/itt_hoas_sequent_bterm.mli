(*
 * Representation of a sequent as a BTerm.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2005-2006 Mojave Group, Caltech
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
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
extends Itt_hoas_sequent

open Basic_tactics

declare SequentRelax{'d}

(*
 * Convert the sequent triple into a BTerm.
 *)
declare sequent_bterm{'d; 's}

(*
 * The type of BTerms that represent sequents.
 *)
declare BSequent{'d}

declare BSequentCore{'d}

declare const BSequentCore

(*
 * Common abbreviations
 *)
define const iform unfold_sequent_relax_zero : SequentRelax <--> SequentRelax{0}
define const iform unfold_BSequent_zero : BSequent <--> BSequent{0}
define iform unfold_sequent_bterm_zero : sequent_bterm{'s} <--> sequent_bterm{0; 's}

(*
 * Relaxed types.
 *)
declare CVarRelax{'n}

(*
 * Convert the BTerm back to a sequent.
 *)
declare sequent_of_bterm{'e}
declare is_sequent_bterm{'e}

(*
 * Internal terms for normalization.
 *)
declare sequent_bterm{'d; 'hyps; 'concl}
declare seq_concl{'e}
declare seq_hyp{'h; x. 't['x]}
declare seq_arg{'arg; 's}

(*
 * Tactics.
 *)
topval fold_is_sequent_bterm_core : conv
topval fold_sequent_of_bterm_core : conv

val sequent_bterm_forward: int -> tactic
val cvar_is_cvar_relax0 : tactic


(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
