doc <:doc<
   @module[Itt_hoas_sequent_bterm]

   Native sequent representation as a << BTerm >>.
   This is computed from the non-BTerm sequent in @tt[Itt_hoas_sequent].

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2005-2006, Mojave Group, Caltech

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

   Author: Jason Hickey @email{jyh@cs.caltech.edu}
   Modified by: Aleksey Nogin @email{nogin@cs.caltech.edu}
   Modified by: Alexei Kopylov @email{kopylov@cs.caltech.edu}
   @end[license]

   @parents
>>
extends Itt_hoas_bterm_wf
extends Itt_hoas_sequent
extends Itt_hoas_relax
extends Itt_dprod
extends Itt_match

doc docoff

open Basic_tactics
open Itt_sqsimple
open Itt_struct
open Itt_hoas_relax

let resource private select +=
   relax_term, OptionAllow

(************************************************************************
 * Relaxed reductions.
 *)
define unfold_CVarRelax : CVarRelax{'d} <--> <:xterm<
   BindTriangle{d}
>>

(*
define const unfold_SequentRelax : SequentRelax <--> <:xterm<
   Bind{0} * Prod hyps: CVarRelax{0} * Bind{length{hyps}}
>>
*)
define unfold_SequentRelax : SequentRelax{'d} <--> <:xterm<
   Bind{d} * Prod hyps: CVarRelax{d} * Bind{length{hyps} +@ 'd}
>>

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

define unfold_sequent_bterm : sequent_bterm{'d; 's} <--> <:xterm<
   dest_sequent{s; arg, hyps, concl.
      $'[d] seq_arg{arg; $,sequent_bterm{d; hyps; concl}}}
>>

(************************************************************************
 * Well-formedness.
 *)
doc <:doc<
   Well-formedness for the relaxed types.
>>
interactive cvar_relax_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- n in nat -->
   <H> >- CVarRelax{n} Type
>>

interactive cvar_relax_is_list {| nth_hyp |} 'H : <:xrule<
   <H>; l: CVarRelax{n}; <J[l]> >- l in list
>>

interactive sequent_relax_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d in nat -->
   <H> >- SequentRelax{d} Type
>>

interactive sequent_relax_elim {| elim [] |} 'H : <:xrule<
   <H>; arg: Bind{d}; hyps: CVarRelax{d}; concl: Bind{length{hyps} +@ d};
      <J["sequent"{arg; hyps; concl}]> >- C["sequent"{arg; hyps; concl}] -->
   <H>; x: SequentRelax{d}; <J[x]> >- C[x]
>>

interactive cvar_is_cvar_relax : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- e in CVar{n} -->
   <H> >- e in CVarRelax{n}
>>

interactive cvar_is_cvar_relax0 {| nth_hyp |} : <:xrule<
   "wf" : <H> >- e in CVar{0} -->
   <H> >- e in CVarRelax{0}
>>

interactive cvar_is_cvar_relax1 {| nth_hyp |} 'H : <:xrule<
   <H>; e: CVar{0}; <J[e]> >- e in CVarRelax{0}
>>

interactive cvar_is_cvar_relax2 {| nth_hyp |} 'H : <:xrule<
   <H>; e: CVar{n}; <J[e]> >- n in nat -->
   <H>; e: CVar{n}; <J[e]> >- e in CVarRelax{n}
>>

interactive nil_is_cvar_relax {| intro |} : <:xrule<
   "wf" : <H> >- n in nat -->
   <H> >- [] in CVarRelax{n}
>>

interactive cons_is_cvar_relax {| intro |} : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- u in Bind{n} -->
   "wf" : <H> >- v in CVarRelax{n +@ 1} -->
   <H> >- u::v in CVarRelax{n}
>>

interactive append_is_cvar_relax {| intro |} : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- u in CVarRelax{n} -->
   "wf" : <H> >- v in CVarRelax{n +@ length{u}} -->
   <H> >- append{u;v} in CVarRelax{n}
>>

interactive cvar_is_bind_list {| nth_hyp |} 'H : <:xrule<
   "wf" : <H>; l: CVar{n}; <J[l]> >- n in nat -->
   <H>; l: CVar{n}; <J[l]> >- l in list{Bind{n}}
>>

interactive sequent_relax_subtype {| intro [] |} :
   ["wf"] sequent{ <H> >- 'd in nat} -->
   sequent{ <H> >- Sequent{'d} subtype SequentRelax{'d} }

interactive sequentRelax_is_sequent {| intro[AutoMustComplete] |} : <:xrule<
   "wf" : <H> >- d in nat -->
   <H> >- s in Sequent{d} -->
   <H> >- s in SequentRelax{d}
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
   sequent_bterm{d; "sequent"{arg; hyps; concl}}
   <-->
   $'[d] seq_arg{arg; $,sequent_bterm{d; hyps; concl}}
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

interactive sequent_bterm_core_relax_wf1 {| intro [] |} : <:xrule<
   "wf" : <H> >- d = n in nat -->
   "wf" : <H> >- hyps in CVar{d} -->
   "wf" : <H> >- concl in BTerm{length{hyps} +@ d} -->
   <H> >- sequent_bterm{d; hyps; concl} in BTerm{n}
>>

interactive sequent_bterm_core_wf2 {| intro [] |} : <:xrule<
   "wf" : <H> >- d in nat -->
   "wf" : <H> >- hyps in CVar{d} -->
   "wf" : <H> >- concl in BTerm{length{hyps} +@ d} -->
   <H> >- sequent_bterm{d; hyps; concl} in BTerm
>>

interactive sequent_bterm_core_relax_wf2 {| intro [] |} : <:xrule<
   "wf" : <H> >- d = n in nat -->
   "wf" : <H> >- hyps in list -->
   <H> >- sequent_bterm{d; hyps; concl} in Bind{n}
>>

interactive sequent_bterm_wf1 {| intro [] |} : <:xrule<
   "wf" : <H> >- s in Sequent{'d} -->
   "wf" : <H> >- d in nat -->
   <H> >- sequent_bterm{d; s} in BTerm{d}
>>

interactive sequent_bterm_wf2 {| intro [] |} : <:xrule<
   "wf" : <H> >- s in Sequent{'d}-->
   "wf" : <H> >- d in nat -->
   <H> >- sequent_bterm{d; s} in BTerm
>>

interactive_rw sequent_bterm_depth0 {| reduce |} : <:xrewrite<
   d in nat -->
   hyps in list -->
   bdepth{sequent_bterm{'d; 'hyps; 'concl}} <--> d
>>

interactive_rw sequent_bterm_depth {| reduce |} : <:xrewrite<
   s in Sequent{d} -->
   d in nat -->
   bdepth{sequent_bterm{d; s}} <--> d
>>

interactive sequent_bterm_equal1 {| intro [] |} : <:xrule<
   "wf" : <H> >- d1 = d2 in nat -->
   "wf" : <H> >- s1 = s2 in Sequent{'d1} -->
   <H> >- sequent_bterm{d1; s1} = sequent_bterm{d2; s2} in BTerm{d1}
>>

interactive sequent_bterm_equal2 {| intro [] |} : <:xrule<
   "wf" : <H> >- d1 = d2 in nat -->
   "wf" : <H> >- s1 = s2 in Sequent{'d1} -->
   <H> >- sequent_bterm{d1; s1} = sequent_bterm{d2; s2} in BTerm
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
            else
               is_same_op{o; $seq_concl{concl}}}) e
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
         else
            is_same_op{o; $seq_concl{concl}}}
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
   h in Bind{d} -->
   rest in Bind{d} -->
   is_sequent_bterm_core{mk_bterm{d; $seq_hyp{h; x. rest}; [h; rest]}}
   <-->
   is_sequent_bterm_core{rest}
>>

interactive_rw reduce_is_sequent_bterm_core_concl {| reduce |} : <:xrewrite<
   d in nat -->
   c in Bind{d} -->
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
   arg in Bind{d} -->
   rest in Bind{d} -->
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
   h in Bind{d} -->
   rest in Bind{d} -->
   sequent_of_bterm_core{mk_bterm{d; $seq_hyp{h; x. rest}; [h; rest]}}
   <-->
   let hyps, concl = sequent_of_bterm_core{rest} in
      (h :: hyps, concl)
>>

interactive_rw reduce_sequent_of_bterm_core_concl {| reduce |} : <:xrewrite<
   d in nat -->
   c in Bind{d} -->
   sequent_of_bterm_core{mk_bterm{d; $seq_concl{c}; [c]}}
   <-->
   ([], c)
>>

interactive_rw reduce_sequent_of_bterm_arg {| reduce |} : <:xrewrite<
   d in nat -->
   arg in Bind{d} -->
   rest in Bind{d} -->
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
   "wf" : <H> >- hyps in CVarRelax{n} -->
   "wf" : <H> >- concl in Bind{n +@ length{hyps}} -->
   <H> >- "assert"{is_sequent_bterm_core{sequent_bterm{n; hyps; concl}}}
>>

interactive sequent_bterm_is_bsequent {| intro [] |} : <:xrule<
   "wf" : <H> >- d in nat -->
   "wf" : <H> >- s in SequentRelax{d} -->
   <H> >- "assert"{is_sequent_bterm{sequent_bterm{d;s}}}
>>

interactive_rw reduce_sequent_of_bterm_core_inverse : <:xrewrite<
   n in nat -->
   hyps in CVarRelax{n} -->
   concl in Bind{n +@ length{hyps}} -->
   sequent_of_bterm_core{sequent_bterm{n; hyps; concl}}
   <-->
   (hyps, concl)
>>

interactive_rw reduce_sequent_of_bterm_inverse : <:xrewrite<
   s in SequentRelax -->
   sequent_of_bterm{sequent_bterm{0; s}}
   <-->
   s
>>

(************************************************************************
 * Elimination.
 *)
doc <:doc<
   Types and elimination forms.

   << BSequentCore >> is the type of hypothesis + conclusion terms.

   << BSequentCore{'n} >> is the same, but it specifies the depth
   of the term.

   << BSequent >> is the type of complete sequents, always depth 0.
>>
define const unfold_BSequentCore : BSequentCore <--> <:xterm<
   { e: BTerm | "assert"{is_sequent_bterm_core{e}} }
>>

interactive bsequent_core_type_wf {| intro [] |} : <:xrule<
   <H> >- BSequentCore Type
>>

interactive bsequent_core_sqsimple {| intro []; sqsimple |} : <:xrule<
   <H> >- sqsimple{BSequentCore}
>>

interactive sequent_bterm_core_bsequent_core_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- hyps in CVar{n} -->
   "wf" : <H> >- concl in BTerm{n +@ length{hyps}} -->
   <H> >- sequent_bterm{n; hyps; concl} in BSequentCore
>>

interactive bsequent_core_elim {| elim [ThinFirst thinT] |} 'H : <:xrule<
   "base" : <H>; x: BSequentCore; <J[x]>; n: nat; c: BTerm{n} >- C[mk_bterm{n; $seq_concl{c}; [c]}] -->
   "step" : <H>; x: BSequentCore; <J[x]>; n: nat; h: BTerm{n}; rest: BTerm{n +@ 1}; C[rest] >- C[mk_bterm{n; $seq_hyp{h; x. rest}; [h; rest]}] -->
   <H>; x: BSequentCore; <J[x]> >- C[x]
>>

define unfold_BSequentCore_depth : BSequentCore{'n} <--> <:xterm<
   { e: BTerm{'n} | "assert"{is_sequent_bterm_core{e}} }
>>

interactive bsequent_core_depth_type_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- n in nat -->
   <H> >- BSequentCore{n} Type
>>

interactive bsequent_core_depth_sqsimple {| intro []; sqsimple |} : <:xrule<
   "wf" : <H> >- n in nat -->
   <H> >- sqsimple{BSequentCore{n}}
>>

interactive sequent_bterm_core_depth_bsequent_core_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- n = m in nat -->
   "wf" : <H> >- hyps in CVar{n} -->
   "wf" : <H> >- concl in BTerm{n +@ length{hyps}} -->
   <H> >- sequent_bterm{n; hyps; concl} in BSequentCore{m}
>>

interactive bsequent_core_depth_elim {| elim [ThinFirst thinT] |} 'H : <:xrule<
   "wf" : <H>; x: BSequentCore{m}; <J[x]> >- m in nat -->
   "base" : <H>; x: BSequentCore{m}; <J[x]>; n: nat; c: BTerm{n} >- C[mk_bterm{n; $seq_concl{c}; [c]}] -->
   "step" : <H>; x: BSequentCore{m}; <J[x]>; n: nat; h: BTerm{n}; rest: BTerm{n +@ 1}; C[rest] >- C[mk_bterm{n; $seq_hyp{h; x. rest}; [h; rest]}] -->
   <H>; x: BSequentCore{m}; <J[x]> >- C[x]
>>

(************************************************
 * BSequent.
 *)
define unfold_BSequent : BSequent{'d} <--> <:xterm<
   { e : BTerm{d} | "assert"{is_sequent_bterm{e}} }
>>

interactive bsequent_type_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d in nat -->
   <H> >- BSequent{'d} Type
>>

interactive bsequent_is_bterm1 {| elim[] |} 'H :
   [wf] sequent { <H>; t: BSequent{'d}; <J['t]> >- 'd in nat } -->
   sequent { <H>; t: BSequent{'d}; <J['t]> >- 't in BTerm }

interactive bsequent_is_bterm2 'd :
   [wf] sequent { <H> >- 'd in nat } -->
   sequent { <H> >- 't in BSequent{'d} } -->
   sequent { <H> >- 't in BTerm }

interactive bsequent_is_bterm_list1 {| elim[] |} 'H :
   [wf] sequent { <H>; t: list{BSequent{'d}}; <J['t]> >- 'd in nat } -->
   sequent { <H>; t: list{BSequent{'d}}; <J['t]> >- 't in list{BTerm} }

interactive bsequent_is_bterm_list2 'd :
   [wf] sequent { <H> >- 'd in nat } -->
   sequent { <H> >- 't in list{BSequent{'d}} } -->
   sequent { <H> >- 't in list{BTerm} }

interactive bsequent_is_bterm0 {| nth_hyp |} 'H :
   sequent { <H>; t: BSequent; <J['t]> >- 't in BTerm }

interactive bsequent_is_bterm_list0 {| nth_hyp |} 'H :
   sequent { <H>; t: list{BSequent}; <J['t]> >- 't in list{BTerm} }

interactive bsequent_is_bterm3 {| nth_hyp |} :
   sequent { <H> >- 't in BSequent{0} } -->
   sequent { <H> >- 't in BTerm }

interactive bsequent_is_bterm_list3 {| nth_hyp |} :
   sequent { <H> >- 't in list{BSequent{0}} } -->
   sequent { <H> >- 't in list{BTerm} }

interactive bsequent_sqsimple {| intro []; sqsimple |} : <:xrule<
   <H> >- d in nat  -->
   <H> >- sqsimple{BSequent{d}}
>>

interactive sequent_bterm_bsequent_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d in nat -->
   "wf" : <H> >- s in Sequent{'d} -->
   <H> >- sequent_bterm{d; s} in BSequent{d}
>>

interactive sequent_bterm_bsequent_equal {| intro [] |} : <:xrule<
   "wf" : <H> >- d1 = d2 in nat -->
   "wf" : <H> >- s1 = s2 in Sequent{'d1} -->
   <H> >- sequent_bterm{d1; s1} = sequent_bterm{d2; s2} in BSequent{d1}
>>

interactive bsequent_type_elim {| elim [] |} 'H : <:xrule<
   "wf" : <H>; x: BSequent{d}; <J[x]> >- d in nat -->
   <H>; arg: BTerm{d}; rest: BSequentCore{d}; <J[mk_bterm{d; $seq_arg{arg; rest}; [arg; rest]}]> >-
      C[mk_bterm{d; $seq_arg{arg; rest}; [arg; rest]}] -->
   <H>; x: BSequent{d}; <J[x]> >- C[x]
>>

(************************************************************************
 * Forward-chaining.
 *)
doc <:doc<
   Forward-chaining.
>>

interactive sequent_bterm_forward_lemma : <:xrule<
   "wf" : <H> >- s in SequentRelax -->
   "wf" : <H> >- sequent_bterm{s} in BTerm -->
   <H> >- s in Sequent
>>

interactive sequent_bterm_forward {| forward |} 'H : <:xrule<
   "wf" : <H>; <J[it]> >- s1 in SequentRelax -->
   "wf" : <H>; <J[it]> >- s2 in SequentRelax -->
   <H>; <J[it]>; s1 = s2 in Sequent >- C[it] -->
   <H>; x: sequent_bterm{s1} = sequent_bterm{s2} in BTerm; <J[x]> >- C[x]
>>

interactive bsequent_core_parts_forward 'H : <:xrule<
   <H>; x: BSequentCore; <J[x]>;
      n: nat;
      hyps: CVar{n};
      concl: BTerm{n +@ length{hyps}};
      x = sequent_bterm{n; hyps; concl} in BSequentCore >- C[x] -->
   <H>; x: BSequentCore; <J[x]> >- C[x]
>>

(*
 * XXX: JYH: we may be able to remove the wf constraint on concl,
 * but in the end it probably isn't important.
 *)
interactive bsequent_core_mem_forward 'H : <:xrule<
   "wf" : <H>; x: sequent_bterm{n; hyps; concl} in BSequentCore; <J[x]> >- n in nat -->
   "wf" : <H>; x: sequent_bterm{n; hyps; concl} in BSequentCore; <J[x]> >- hyps in CVarRelax{n} -->
   "wf" : <H>; x: sequent_bterm{n; hyps; concl} in BSequentCore; <J[x]> >- concl in Bind{n +@ length{hyps}} -->
   <H>; x: sequent_bterm{n; hyps; concl} in BSequentCore; <J[x]>;
      hyps in CVar{n};
      concl in BTerm{n +@ length{hyps}} >- C[x] -->
   <H>; x: sequent_bterm{n; hyps; concl} in BSequentCore; <J[x]> >- C[x]
>>

(*
 * XXX: JYH: currently the proof is pretty sloppy.
 *)
interactive bsequent_bterm_forward 'H : <:xrule<
   "wf" : <H>; <J[it]> >- hyps in CVarRelax{0} -->
   "wf" : <H>; <J[it]> >- concl in Bind{length{hyps}} -->
   <H>; <J[it]>;
      arg in BTerm{0};
      hyps in CVar{0};
      concl in BTerm{length{hyps}}
      >- C[it] -->
   <H>; x: sequent_bterm{"sequent"{arg; hyps; concl}} in BSequent; <J[x]> >- C[x]
>>

doc docoff

(************************************************************************
 * Tactics.
 *)
let fold_is_sequent_bterm_core = makeFoldC <:xterm< is_sequent_bterm_core{e} >> unfold_is_sequent_bterm_core
let fold_sequent_of_bterm_core = makeFoldC <:xterm< sequent_of_bterm_core{e} >> unfold_sequent_of_bterm_core

(************************************************************************
 * Common abbreviations
 *)
doc docon
define const iform unfold_sequent_relax_zero: SequentRelax <--> SequentRelax{0}
define iform unfold_sequent_bterm_zero: sequent_bterm{'s} <--> sequent_bterm{0; 's}
define const iform unfold_BSequent_zero: BSequent <--> BSequent{0}
doc docoff

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
