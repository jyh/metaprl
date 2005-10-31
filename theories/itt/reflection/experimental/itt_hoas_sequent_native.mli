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
declare Sequent{'d; 'ty_arg; 'ty_hyp; 'ty_concl}

(*
 * A second-order variable of type 'ty.
 *)
declare SOVar{'d; 'ty}

(*
 * A sequent context variable.
 *)
declare CVar{'d; 'ty_hyp}

(*
 * A step in a proof.
 *)
declare ProofStep{'ty_sequent}

(*
 * Predicates on sequents.
 *)
topval fold_hyp_depths : conv

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
