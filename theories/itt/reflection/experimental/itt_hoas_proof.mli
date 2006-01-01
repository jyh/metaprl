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
 * A step in a proof.
 *)
declare ProofStep{'ty_sequent}
declare ProofStepWitness
declare proof_step{'premises; 'goal}
declare proof_step_witness{'sovars; 'cvars}

(*
 * A checking rule for a single step of a proof.
 *)
declare ProofRule{'ty_sequent}

(*
 * A Logic is a list of ProofRules.
 *)
declare Logic{'rules}

(*
 * A formula is provable in a logic.
 *)
declare Provable{'ty_sequent; 'logic; 't}

(*
 * Logic operations.
 *)
declare empty_logic
declare rules_logic{'r; 'logic}
declare union_logic{'logic1; 'logic2}

(*
 * One logic is included in another.
 *)
declare SubLogic{'ty; 'logic1; 'logic2}

(*
 * Rewrites.
 *)
topval fold_Logic : conv
topval fold_Derivation_indexed : conv
topval fold_derivation_depth : conv
topval fold_derivation_step : conv
topval fold_proof_step : conv
topval fold_proof_step_witness : conv

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
