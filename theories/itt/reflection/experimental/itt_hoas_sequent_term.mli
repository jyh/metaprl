doc <:doc<
   Native sequent representation.  This representation of sequents
   is not a BTerm itself.  If you want to work in a theory where
   sequents are not part of your language, then you should probably
   use this representation, because it is easier to use.

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
extends Itt_hoas_vbind
extends Itt_hoas_sequent
extends Itt_vec_sequent_term
extends Itt_vec_list1

open Basic_tactics

(*
 * Individual hypotheses.
 *)
declare sequent [hyp_term] { Term : Term >- Term } : Term

(*
 * Context variables are represented with the << hyp_context >> term.
 *)
declare sequent [hyp_context] { Term : Term >- Term } : Term

(*
 * BTerm sequent.  Hyps are in normal "pretty" form.
 *)
declare sequent [bsequent{'arg}] { Term : Term >- Term } : Term

(*
 * BTerm sequent.  Hyps are in "ugly" form.
 *)
declare sequent [vsequent{'arg}] { Term : Term >- Term } : Term

(*
 * ML code.
 *)
topval fold_hyp_term : conv
topval fold_hyp_context : conv
topval fold_bterm_of_vterm : conv

topval reduce_bsequent : conv
topval reduce_vsequent : conv

topval forward_bsequent_wf : int -> tactic

(*
 * Terms.
 *)
val is_vsequent_term : term -> bool
val dest_vsequent_term : term -> term * seq_hyps * term

val is_hyp_context_term : term -> bool
val dest_hyp_context_term : term -> seq_hyps * term

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
