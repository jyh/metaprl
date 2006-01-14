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
extends Itt_dprod
extends Itt_match

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

interactive_rw reduce_sequent_bterm_sequent {| reduce |} : <:xrewrite<
   sequent_bterm{"sequent"{arg; hyps; concl}}
   <-->
   $`seq_arg{arg; $,sequent_bterm{0; hyps; concl}}
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

(************************************************************************
 * Inversion.
 *)
doc <:doc<
   Also define an inversion that produces the original << Sequent >> term from the
   << BTerm >>.
>>
define unfold_is_sequent_bterm_core : is_sequent_bterm_core{'e} <--> <:xterm<
   (fix f e ->
      "dest_bterm"{e;
         l, r. bfalse;
         d, o, s.
            if is_same_op{o; $seq_hyp{h; x. rest}} then
               f nth{s; 1}
            else if is_same_op{o; $seq_concl{concl}} then
               btrue
            else
               bfalse}) e
>>

define unfold_is_sequent_bterm : is_sequent_bterm{'e} <--> <:xterm<
   "dest_bterm"{e;
      l, r. bfalse;
      d, o, s.
         is_same_op{o; $seq_arg{arg; rest}} &&b is_sequent_bterm_core{nth{s; 1}}}
>>

define unfold_sequent_of_bterm_core : sequent_of_bterm_core{'e} <--> <:xterm<
   (fix f e ->
      "dest_bterm"{e;
         l, r. it;
         d, o, s.
            if is_same_op{o; $seq_hyp{h; x. rest}} then
               let hyps, concl = f nth{s; 1} in
                  (nth{s; 0} :: hyps, concl)
            else (* is_same_op{o; $seq_concl{concl}} *)
               ([], nth{s; 0})}) e
>>

define unfold_sequent_of_bterm : sequent_of_bterm{'e} <--> <:xterm<
   "dest_bterm"{e;
      l, r. it;
      d, o, s.
         let hyps, concl = sequent_of_bterm_core{nth{s; 1}} in
            "sequent"{nth{s; 0}; hyps; concl}}
>>

(************************************************
 * Rewrites.
 *)
doc <:doc<
   Rewrites for << is_sequent_bterm{'e} >>.
>>
interactive_rw reduce_is_sequent_bterm_core : <:xrewrite<
   is_sequent_bterm_core{e}
   <-->
   "dest_bterm"{e;
      l, r. bfalse;
      d, o, s.
         if is_same_op{o; $seq_hyp{h; x. rest}} then
            is_sequent_bterm_core{nth{s; 1}}
         else if is_same_op{o; $seq_concl{concl}} then
            btrue
         else
            bfalse}
>>

interactive_rw reduce_is_sequent_bterm_core_var {| reduce |} : <:xrewrite<
   l in nat -->
   r in nat -->
   is_sequent_bterm_core{var{l; r}}
   <-->
   bfalse
>>

interactive_rw reduce_is_sequent_bterm_core_hyp {| reduce |} : <:xrewrite<
   d in nat -->
   h in BTerm{d} -->
   rest in BTerm{d +@ 1} -->
   is_sequent_bterm_core{mk_bterm{d; $seq_hyp{h; x. rest}; [h; rest]}}
   <-->
   is_sequent_bterm_core{rest}
>>

interactive_rw reduce_is_sequent_bterm_core_concl {| reduce |} : <:xrewrite<
   d in nat -->
   c in BTerm{d} -->
   is_sequent_bterm_core{mk_bterm{d; $seq_concl{c}; [c]}}
   <-->
   btrue
>>

interactive_rw reduce_is_sequent_bterm_var {| reduce |} : <:xrewrite<
   l in nat -->
   r in nat -->
   is_sequent_bterm{var{l; r}}
   <-->
   bfalse
>>

interactive_rw reduce_is_sequent_bterm_arg {| reduce |} : <:xrewrite<
   d in nat -->
   arg in BTerm{d} -->
   rest in BTerm{d} -->
   is_sequent_bterm{mk_bterm{d; $seq_arg{arg; rest}; [arg; rest]}}
   <-->
   is_sequent_bterm_core{rest}
>>

(************************************************
 * sequent_of_bterm.
 *)
doc <:doc<
   Rewrites for << sequent_of_bterm{'e} >>.
>>
interactive_rw reduce_sequent_of_bterm_core : <:xrewrite<
   sequent_of_bterm_core{e}
   <-->
   "dest_bterm"{e;
      l, r. it;
      d, o, s.
         if is_same_op{o; $seq_hyp{h; x. rest}} then
            let hyps, concl = sequent_of_bterm_core{nth{s; 1}} in
               (nth{s; 0} :: hyps, concl)
         else (* is_same_op{o; $seq_concl{concl}} *)
            ([], nth{s; 0})}
>>

interactive_rw reduce_sequent_of_bterm_core_hyp {| reduce |} : <:xrewrite<
   d in nat -->
   h in BTerm{d} -->
   rest in BTerm{d +@ 1} -->
   sequent_of_bterm_core{mk_bterm{d; $seq_hyp{h; x. rest}; [h; rest]}}
   <-->
   let hyps, concl = sequent_of_bterm_core{rest} in
      (h :: hyps, concl)
>>

interactive_rw reduce_sequent_of_bterm_core_concl {| reduce |} : <:xrewrite<
   d in nat -->
   c in BTerm{d} -->
   sequent_of_bterm_core{mk_bterm{d; $seq_concl{c}; [c]}}
   <-->
   ([], c)
>>

interactive_rw reduce_sequent_of_bterm_arg {| reduce |} : <:xrewrite<
   d in nat -->
   arg in BTerm{d} -->
   rest in BTerm{d} -->
   sequent_of_bterm{mk_bterm{d; $seq_arg{arg; rest}; [arg; rest]}}
   <-->
   let hyps, concl = sequent_of_bterm_core{rest} in
      "sequent"{arg; hyps; concl}
>>

(************************************************
 * Well-formedness.
 *)
doc <:doc<
   Well-formedness.
>>
interactive is_sequent_bterm_core_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- e in BTerm -->
   <H> >- is_sequent_bterm_core{e} in bool
>>

interactive is_sequent_bterm_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- e in BTerm -->
   <H> >- is_sequent_bterm{e} in bool
>>

interactive sequent_of_bterm_core_wf1 {| intro [] |} : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- e in BTerm{n} -->
   "aux" : <H> >- "assert"{is_sequent_bterm_core{e}} -->
   <H> >- sequent_of_bterm_core{e} in (Prod hyps: CVar{n} * BTerm{n +@ length{hyps}})
>>

interactive sequent_of_bterm_wf1 {| intro [] |} : <:xrule<
   "wf" : <H> >- e in BTerm{0} -->
   "aux" : <H> >- "assert"{is_sequent_bterm{e}} -->
   <H> >- sequent_of_bterm{e} in Sequent
>>

(************************************************************************
 * Inversion rewrites.
 *)
doc <:doc<
   Show that the << sequent_bterm{'e} >> and << sequent_of_bterm{'e} >> are inverses
   of each other.
>>
interactive sequent_bterm_core_is_bsequent_core {| intro [] |} : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- hyps in CVar{n} -->
   "wf" : <H> >- concl in BTerm{n +@ length{hyps}} -->
   <H> >- "assert"{is_sequent_bterm_core{sequent_bterm{n; hyps; concl}}}
>>

interactive sequent_bterm_is_bsequent {| intro [] |} : <:xrule<
   "wf" : <H> >- s in Sequent -->
   <H> >- "assert"{is_sequent_bterm{sequent_bterm{s}}}
>>

interactive_rw reduce_sequent_of_bterm_core_inverse : <:xrewrite<
   n in nat -->
   hyps in CVar{n} -->
   concl in BTerm{n +@ length{hyps}} -->
   sequent_of_bterm_core{sequent_bterm{n; hyps; concl}}
   <-->
   (hyps, concl)
>>

interactive_rw reduce_sequent_of_bterm_inverse : <:xrewrite<
   s in Sequent -->
   sequent_of_bterm{sequent_bterm{s}}
   <-->
   s
>>

(************************************************************************
 * The BSequent type.
 *)
define const unfold_BSequent : BSequent <--> <:xterm<
   { e: BTerm{0} | "assert"{is_sequent_bterm{e}} }
>>

interactive bsequent_wf {| intro [] |} : <:xrule<
   <H> >- BSequent Type
>>

interactive bterm_of_sequent_wf2 {| intro [] |} : <:xrule<
   "wf" : <H> >- s in Sequent -->
   <H> >- sequent_bterm{s} in BSequent
>>

interactive bterm_of_sequent_equal {| intro [] |} : <:xrule<
   "wf" : <H> >- s1 = s2 in Sequent -->
   <H> >- sequent_bterm{s1} = sequent_bterm{s2} in BSequent
>>

(************************************************************************
 * Tactics.
 *)
let fold_is_sequent_bterm_core = makeFoldC <:xterm< is_sequent_bterm_core{e} >> unfold_is_sequent_bterm_core
let fold_sequent_of_bterm_core = makeFoldC <:xterm< sequent_of_bterm_core{e} >> unfold_sequent_of_bterm_core

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
