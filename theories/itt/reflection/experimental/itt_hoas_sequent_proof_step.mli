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
extends Itt_hoas_sequent
extends Itt_hoas_proof

open Basic_tactics

(*
 * Equality on proof steps in a sequent logic.
 *)
declare beq_proof_step{'step1; 'step2}

(*
 * Proof-step destructors.
 *)
declare let_sovar{'d; 'witness; 'i; v. 'e}
declare let_cvar{'d; 'witness; 'i; v. 'e}

(*
 * Tactics.
 *)
val is_beq_proof_step_term : term -> bool
val dest_beq_proof_step_term : term -> term * term

val is_let_cvar_term : term -> bool
val dest_let_cvar_term : term -> term * term * term * var * term

val is_let_sovar_term : term -> bool
val dest_let_sovar_term : term -> term * term * term * var * term

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
