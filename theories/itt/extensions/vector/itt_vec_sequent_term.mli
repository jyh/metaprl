doc <:doc<
   Sequent flattening.

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2005 Mojave Group, Caltech

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
   @end[license]

   @parents
>>
extends Itt_vec_bind

open Basic_tactics

(*
 * Flatten a binder over a list of hyps.
 *)
declare hyps_flatten{'e}

(*
 * A list of hypotheses.
 *)
declare sequent [hyplist] { Term : Term >- Term } : Term

(*
 * Compute the flat representation of a sequent.
 *)
declare sequent [fsequent{'arg}] { Term : Term >- Term } : Term

(*
 * ML values.
 *)
topval fold_hyps_length : conv
topval fold_hyps_nth : conv
topval fold_hyps_flatten : conv
topval fold_hypconslist : conv
topval fold_hyplist : conv

(*
 * Tactics.
 *)
topval hoistHypsLengthT : tactic
topval reduce_fsequent : conv

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
