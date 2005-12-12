doc <:doc<
   Native sequent representation, based on Itt_vec_sequent_term.fsequent.

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
extends Itt_hoas_vbind
extends Itt_hoas_sequent
extends Itt_match

doc docoff

open Basic_tactics

(************************************************************************
 * Itt_vec_bind --> Itt_hoas_vbind conversion.
 *)
doc <:doc<
   Define a conversion from @tt[Itt_vec_bind] terms to BTerms.
>>
define unfold_bterm_of_vterm :
   bterm_of_vterm{'e}
   <-->
   fix{f. lambda{e. dest_bind{'e; bind{x. 'f bind_subst{'e; 'x}}; x. 'e}}} 'e

interactive_rw reduce_bterm_of_mk_bind {| reduce |} :
   bterm_of_vterm{mk_bind{x. 'e['x]}}
   <-->
   bind{x. bterm_of_vterm{'e['x]}}

interactive_rw reduce_bterm_of_mk_term {| reduce |} :
   bterm_of_vterm{mk_term{'op; 'subterms}}
   <-->
   mk_term{'op; 'subterms}

interactive_rw reduce_bterm_of_mk_vbind {| reduce |} :
   bterm_of_vterm{mk_vbind{| <J> >- 'C |}}
   <-->
   vbind{| <J> >- bterm_of_vterm{'C} |}

(************************************************************************
 * Well-formedness.
 *)
declare sequent [sequent_wf] { Term : Term >- Term } : Term

(************************************************************************
 * The wf theorem.
 *)
interactive bsequent_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- arg IN BTerm{0} -->
   "wf" : <H> >- "sequent_wf"{| <J> >- C |} -->
   <H> >- bsequent{arg}{| <J> >- C |} IN "Sequent"
>>

(************************************************************************
 * Tactics.
 *)
let fold_bterm_of_vterm = makeFoldC << bterm_of_vterm{'e} >> unfold_bterm_of_vterm

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
