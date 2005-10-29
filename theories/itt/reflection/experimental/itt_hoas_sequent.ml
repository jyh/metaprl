doc <:doc<
   Reflected sequents.

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
   Sequents are reflected in Term_std form.  That is, a sequent is
   sequence of hypotheses << hyp{'e; x. 'rest} >>, and a single
   conclusion << concl{'e} >>.
>>
declare hyp{'e; x. 'rest['x]}
declare concl{'e}

doc docoff

(************************************************************************
 * Display.
 *)
dform hyp_df : <:xterm< $`[d] hyp{e; x. rest} >> =
   slot{'x} `":[" slot{'d} `"] " slot{'e} `";" hspace slot{'rest}

dform concl_df : <:xterm< $`[d] concl{e} >> =
   `">-[" slot{'d} `"] " slot{'e}

(************************************************************************
 * Combinators.
 *)
doc <:doc<
   Frequently, we need a predicate to determine if a sequent is well-formed.
   It needs to be a sequence of hypotheses followed by a conclusion, all
   properly nested and with the right depths.

   First, we define an induction combinator.
>>
define unfold_dest_sequent :
    dest_sequent{'e;
       e, rest. 'hyp['e; 'rest];
       e. 'concl['e];
       'other}
    <-->
    dest_bterm{'e;
       l, r. 'other;
       d, o, s.
          if is_same_op{'o; operator[(hyp{'e; x. 'rest['x]}):op]} then
             'hyp[nth{'s; 0}; nth{'s; 1}]
          else if is_same_op{'o; operator[(concl{'e}):op]} then
             'concl[nth{'s; 0}]
          else
             'other}
doc docoff

interactive_rw reduce_var {| reduce |} : <:xrewrite<
   l IN "nat" -->
   r IN "nat" -->
   dest_sequent{var{l; r};
       e, rest. hyp[e; rest];
       e. concl[e];
       other}
   <-->
   other
>>

interactive_rw reduce_hyp {| reduce |} : <:xrewrite<
   d IN "nat" -->
   e IN BTerm{} -->
   bind{x. rest[x]} IN BTerm{} -->
   bdepth{e} = d in "nat" -->
   bdepth{rest["dummy"]} = d in "nat" -->

   dest_sequent{$`[d] hyp{e; x. rest[x]};
       e, rest. hyp[e; rest];
       e. concl[e];
       other}
   <-->
   hyp[e; bind{x. rest[x]}]
>>

interactive_rw reduce_concl {| reduce |} : <:xrewrite<
   d IN "nat" -->
   e IN BTerm{} -->
   bdepth{e} = d in "nat" -->

   dest_sequent{$`[d] concl{e};
       e, rest. hyp[e; rest];
       e. concl[e];
       other}
   <-->
   concl[e]
>>

doc <:doc<
   The induction combinator is total over all terms in << BTerm >>.
>>
interactive dest_sequent_type {| intro [] |} : <:xrule<
   "wf" : <H> >- e1 IN BTerm{} -->
   "wf" : <H>; e: BTerm{}; rest: BTerm{}; bdepth{rest} = bdepth{e} +@ 1 in nat{} >- hyp[e; rest] Type -->
   "wf" : <H>; e: BTerm{} >- concl[e] Type -->
   "wf" : <H> >- other Type -->
   <H> >- dest_sequent{e1; e, rest. hyp[e; rest]; e. concl[e]; other} Type
>>

doc <:doc<
   Define a predicate for valid sequents.
>>
define unfold_is_sequent : is_sequent{'e} <--> <:xterm<
   (fix is_sequent e ->
      dest_sequent{e;
         e, rest. is_sequent rest;
         e. "true";
         "false"}) e
>>

let fold_is_sequent = makeFoldC << is_sequent{'e} >> unfold_is_sequent

interactive is_sequent_type {| intro [] |} : <:xrule<
   "wf" : <H> >- e IN "BTerm" -->
   <H> >- is_sequent{e} Type
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
