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
 * An actual sequent term.
 *)
declare "sequent"{'arg; 'hyps; 'concl}

(*
 * The type of sequents.
 *)
declare Sequent
declare beq_sequent{'s1; 's2}
declare beq_sequent_list{'l1; 's2}

(*
 * A second-order variable of type 'ty.
 *)
declare SOVar{'d}

(*
 * A sequent context variable.
 *)
declare CVar{'d}

(*
 * A checking rule for a single step of a proof.
 *)
declare ProofRule{'ty_sequent}

(*
 * A step in a proof.
 *)
declare ProofStep{'ty_sequent}
declare proof_step{'premises; 'goal}
declare beq_proof_step{'step1; 'step2}

(*
 * A Logic is a list of ProofRules.
 *)
declare Logic{'rules}

(*
 * A formula is provable in a logic.
 *)
declare Provable{'ty_sequent; 'logic; 't}

(*
 * Hypothesis depth check.
 *)
declare hyp_depths{'d; 'hyps}

(*
 * Rewrites.
 *)
topval fold_sequent : conv
topval fold_hyp_depths : conv
topval fold_Logic : conv
topval fold_Derivation_indexed : conv
topval fold_derivation_depth : conv
topval fold_derivation_step : conv
topval fold_proof_step : conv
topval fold_beq_sequent_list : conv

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
