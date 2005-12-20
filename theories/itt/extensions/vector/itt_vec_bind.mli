(*
 * A sequent-style vector binding.
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
extends Itt_theory

open Basic_tactics

(*
 * A single binder.
 *)
declare mk_bind{x. 'e}
declare mk_core{'e}
declare dest_bind{'e; 'bind; x. 'core['e]}
declare bind_subst{'e1; 'e2}

(*
 * The binder.
 *)
declare sequent [mk_vbind] { Term : Term >- Term } : Term

(*
 * A dummy substitution.
 *)
declare sequent [vsubst_dummy] { Term : Term >- Term } : Term

(*
 * List bindings.
 *)
declare mk_lbind{'n; x. 'e['x]}
declare bind_substl{'e; 'l}
declare sequent [vbind_arity] { Term : Term >- Term } : Term

(*
 * Tactics.
 *)
topval wrapVBindT : tactic

topval pushVBindSubstC : term -> conv
topval reduceVBindC : conv

(*
 * Term operations.
 *)
val is_mk_vbind_term : term -> bool
val mk_mk_vbind_term : seq_hyps -> term -> term
val dest_mk_vbind_term : term -> seq_hyps * term

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
