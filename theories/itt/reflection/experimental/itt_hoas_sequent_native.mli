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

(*
 * A second-order variable of type 'ty.
 *)
declare SOVar{'d}

(*
 * A sequent context variable.
 *)
declare CVar{'d}

(*
 * A step in a proof.
 *)
declare ProofStep{'ty_sequent}

(*
 * A Logic is a list of rules.
 *)
declare Logic{'rules}

(*
 * Rewrites.
 *)
topval fold_hyp_depths : conv
topval fold_Logic : conv
topval fold_Derivation_indexed : conv
topval fold_DerivationDepth : conv
topval fold_DerivationStep : conv

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
