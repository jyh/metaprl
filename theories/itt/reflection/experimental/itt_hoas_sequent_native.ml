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
extends Itt_match
extends Itt_hoas_util

doc docoff

open Basic_tactics

doc <:doc<
   A sequent is represented as a 3-tuple << BTerm * list{BTerm} * BTerm >>,
   where the first term is the argument, the second is the hypotheses,
   and the final term is the conclusion.

   We have several constraints.  In a sequent (arg, hyps, concl), the
   hyps must have depths increasing by 1, and the conclusion must have the
   depth of the final hypothesis + 1.
>>
define unfold_sequent : "sequent"{'arg; 'hyps; 'concl} <-->
   ('arg, ('hyps, 'concl))

define unfold_hyp_depths : hyp_depths{'d; 'l} <-->
   list_ind{'l; lambda{d. "true"}; h, t, g. lambda{d. bdepth{'h} = 'd in nat & 'g ('d +@ 1)}} 'd

define unfold_is_sequent : is_sequent{'d; 's} <-->
   spread{'s; arg, rest. spread{'rest; hyps, concl.
      bdepth{'arg} = 'd in nat
      & hyp_depths{'d; 'hyps}
      & bdepth{'concl} = 'd +@ length{'hyps} in nat}}

define unfold_SOVar : SOVar{'d} <-->
   { e: BTerm | bdepth{'e} = 'd in nat }

define unfold_CVar : CVar{'d} <-->
   { l: list{BTerm} | hyp_depths{'d; 'l} }

define unfold_ProofStep : ProofStep <-->
   list{BTerm} * BTerm
doc docoff

let fold_hyp_depths = makeFoldC << hyp_depths{'d; 'l} >> unfold_hyp_depths

interactive hyp_depths_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   "wf" : <H> >- l IN list{"BTerm"} -->
   <H> >- hyp_depths{d; l} Type
>>

interactive is_sequent_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   "wf" : <H> >- s IN "BTerm" * list{"BTerm"} * "BTerm" -->
   <H> >- is_sequent{d; s} Type
>>

interactive is_sequent_wf2 {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   "wf" : <H> >- arg IN "BTerm" -->
   "wf" : <H> >- hyps IN list{"BTerm"} -->
   "wf" : <H> >- concl IN "BTerm" -->
   <H> >- is_sequent{d; "sequent"{arg; hyps; concl}} Type
>>

doc <:doc<
   Sequents are represented by triples that are valid.
>>
define unfold_Sequent : Sequent{'d} <--> <:xterm<
   { s: ("BTerm" * list{"BTerm"} * "BTerm") | is_sequent{d; s} }
>>
doc docoff

interactive sequent_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   <H> >- Sequent{d} Type
>>

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
