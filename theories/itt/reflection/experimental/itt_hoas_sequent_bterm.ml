doc <:doc<
   Native sequent representation as a << BTerm >>.
   This is computed from the non-BTerm sequent in @tt[Itt_hoas_sequent].

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
extends Itt_hoas_sequent

doc docoff

open Basic_tactics

(************************************************************************
 * Terms.
 *)
doc <:doc<
   Given a sequent << sequent ['arg] { x1: 't1; x2: 't2; math_ldots; xn: 'tn >- 'c } >>,
   the ``standard'' BTerm representation is as follows.

   << seq_arg{'arg; seq_hyp{'t1; x1. math_ldots seq_hyp{'tn; xn. seq_concl{'c}}}} >>.
>>

declare seq_arg{'arg; 'seq}
declare seq_hyp{'hyp; x. 'rest['x]}
declare seq_concl{'concl}

define unfold_sequent_bterm_core : sequent_bterm{'d; 'hyps; 'concl} <--> <:xterm<
   list_ind{hyps;
       lambda{d. $'[d] seq_concl{concl}};
       u, v, g. lambda{d. mk_bterm{d; $seq_hyp{h; x. r}; [u; g (d +@ 1)]}}} d
>>

define unfold_sequent_bterm : sequent_bterm{'s} <--> <:xterm<
   dest_sequent{s; arg, hyps, concl.
      $`seq_arg{arg; $,sequent_bterm{0; hyps; concl}}}
>>

(************************************************************************
 * Rewrites.
 *)
doc <:doc<
   Rewrites.
>>
interactive_rw reduce_sequent_bterm_core_nil {| reduce |} : <:xrewrite<
   sequent_bterm{d; []; concl}
   <-->
   $'[d] seq_concl{concl}
>>

interactive_rw reduce_sequent_bterm_core_cons {| reduce |} : <:xrewrite<
   sequent_bterm{d; u::v; concl}
   <-->
   mk_bterm{d; $seq_hyp{h; x. r}; [u; sequent_bterm{d +@ 1; v; concl}]}
>>

(************************************************************************
 * Well-formedness.
 *)
doc <:doc<
   Well-formedness.
>>
interactive sequent_bterm_core_wf1 {| intro [] |} : <:xrule<
   "wf" : <H> >- d in nat -->
   "wf" : <H> >- hyps in CVar{d} -->
   "wf" : <H> >- concl in BTerm{length{hyps} +@ d} -->
   <H> >- sequent_bterm{d; hyps; concl} in BTerm{d}
>>

interactive sequent_bterm_core_wf2 {| intro [] |} : <:xrule<
   "wf" : <H> >- d in nat -->
   "wf" : <H> >- hyps in CVar{d} -->
   "wf" : <H> >- concl in BTerm{length{hyps} +@ d} -->
   <H> >- sequent_bterm{d; hyps; concl} in BTerm
>>

interactive sequent_bterm_wf1 {| intro [] |} : <:xrule<
   "wf" : <H> >- s in Sequent -->
   <H> >- sequent_bterm{s} in BTerm{0}
>>

interactive sequent_bterm_wf2 {| intro [] |} : <:xrule<
   "wf" : <H> >- s in Sequent -->
   <H> >- sequent_bterm{s} in BTerm
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
