(*
 * Native sequent representation.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2005 Mojave Group, Caltech
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
extends Itt_hoas_util

open Basic_tactics

(*
 * Sequents and their types.
 *)
declare "sequent"{'arg; 'hyps; 'concl}
declare sequent_arg{'s}
declare sequent_hyps{'s}
declare sequent_concl{'s}
declare dest_sequent{'s; arg, hyps, concl. 'e['arg; 'hyps; 'concl]}

declare beq_sequent{'s1; 's2}
declare beq_sequent_list{'l1; 's2}

(*
 * A sequent with depth 'd.
 *)
declare Sequent{'d}
declare is_sequent{'d;'e}

declare const Sequent
declare is_sequent{'e}

(*
 * A sequent context variable at depth 'd.
 *)
declare CVar{'d}

(*
 * Hypothesis depth check.
 *)
declare hyp_depths{'d; 'hyps}
declare bhyp_depths{'d; 'hyps}

(*
 * Rewrites.
 *)
topval fold_sequent : conv
topval fold_hyp_depths : conv
topval fold_bhyp_depths : conv
topval fold_beq_sequent_list : conv

topval unfold_is_sequent : conv
topval unfold_Sequent : conv

(*
 * Tactics.
 *)
val is_beq_sequent_term : term -> bool
val dest_beq_sequent_term : term -> term * term


(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
