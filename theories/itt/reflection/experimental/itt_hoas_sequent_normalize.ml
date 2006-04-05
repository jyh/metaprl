(*
 * Sequent normalization.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2006 Mojave Group, Caltech
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
extends Itt_hoas_sequent_term
extends Itt_hoas_sequent_bterm
extends Itt_hoas_normalize
extends Itt_hoas_lof_vec

doc docoff

open Lm_printf

open Basic_tactics

open Itt_list2

open Itt_vec_util

open Itt_hoas_lof
open Itt_hoas_lof_vec
open Itt_hoas_normalize

(************************************************************************
 * Map a bind over a list.
 *)
define unfold_bind_length : bind_length{'e} <--> <:xterm<
   (fix f e -> weak_dest_terms{e; f subst{e; it}; l. length{l}}) e
>>

define unfold_bind_nth : bind_nth{'e; 'i} <--> <:xterm<
   (fix f e -> weak_dest_terms{e; bind{x. f subst{e; x}}; l. nth{l; i}}) e
>>

define unfold_bind_flatten : bind_flatten{'e} <--> <:xterm<
   list_of_fun{i. bind_nth{e; i}; bind_length{e}}
>>

declare sequent [vbind_map] { Term : Term >- Term } : Term

prim_rw unfold_vbind_map : vbind_map{| <J> >- 'e |} <--> <:xterm<
   bind_flatten{vbind{| <J> >- mk_terms{e} |}}
>>

(************************************************************************
 * sequent_bterm normalization.
 *)
interactive_rw reduce_vbind_sequent_bterm_core_nil : <:xrewrite<
   vbind{| <J> >- sequent_bterm{d<||>; []; concl} |}
   <-->
   vbind{| <J> >- $'[d]seq_concl{concl} |}
>>

interactive_rw reduce_vbind_sequent_bterm_core_cons : <:xrewrite<
   d in nat -->
   vbind{| <J> >- sequent_bterm{d<||>; h :: hyps; concl} |}
   <-->
   mk_bterm{d +@ length{vlist{| <J> |}}; $seq_hyp{h; x. r};
      [vbind{| <J> >- h |}; vbind{| <J> >- sequent_bterm{d +@ 1; hyps; concl} |}]}
>>

interactive_rw reduce_vbind_sequent_bterm : <:xrewrite<
   d in nat -->
   vbind{| <J> >- sequent_bterm{d<||>; "sequent"{arg; hyps; concl}} |}
   <-->
   mk_bterm{d +@ length{vlist{| <J> |}}; $seq_arg{arg; s};
      [vbind{| <J> >- arg |}; vbind{| <J> >- sequent_bterm{d; hyps; concl} |}]}
>>

(************************************************************************
 * vsequent normalization.x
 *
 * Pre-normalize:
 *    - convert the hyps to a lof
 *)
declare sequent [lof_vsequent{'arg}] { Term : Term >- Term } : Term

prim_rw unfold_lof_vsequent : <:xrewrite<
   lof_vsequent{arg}{| <J> >- e |}
   <-->
   vsequent{arg}{| <J> >- e |}
>>

interactive_rw pre_normalize_vsequent {| pre_normalize_lof |} : <:xrewrite<
   vsequent{arg}{| <J> >- concl |}
   <-->
   lof_vsequent{arg}{| lof{i. lof_nil; 0}; <J> >- concl |}
>>

interactive_rw hyp_term_lof : <:xrewrite<
   hyp_term{| <K> >- h |}
   <-->
   lof{i. lof_nth{hyp_term{| <K> >- h |}; i}; 1}
>>

interactive_rw vsequent_hyp_term_lof : <:xrewrite<
   n in nat -->
   lof_vsequent{arg}{| lof{i. f[i]; n}; hyp_term{| <K> >- h |}; <J> >- concl |}
   <-->
   lof_vsequent{arg}{| lof{i.
      lof_append{i. f[i];
                 i. lof_nth{hyp_term{| <K> >- h |}; i};
                 i;
                 n;
                 1};
      n +@ 1}; <J> >- concl |}
>>

interactive_rw hyp_context_lof : <:xrewrite<
   hyp_context{| <J> >- hyplist{| <K> |} |}
   <-->
   lof{i. lof_nth{hyp_context{| <J> >- hyplist{| <K> |} |}; i}; length{hyp_context{| <J> >- hyplist{| <K> |} |}}}
>>

interactive_rw vsequent_hyp_context_lof : <:xrewrite<
   n in nat -->
   lof_vsequent{arg}{| lof{i. f[i]; n}; hyp_context{| <K> >- hyplist{| <L> |} |}; <J> >- concl |}
   <-->
   lof_vsequent{arg}{| lof{i.
      lof_append{i. f[i];
                 i. lof_nth{hyp_context{| <K> >- hyplist{| <L> |} |}; i};
                 i;
                 n;
                 length{hyp_context{| <K> >- hyplist{| <L> |} |}}};
      n +@ length{hyp_context{| <K> >- hyplist{| <L> |} |}}}; <J> >- concl |}
>>

(************************************************************************
 * Length pushing.
 *)
declare sequent [squash_vbind] { Term : Term >- Term } : Term

prim_rw unfold_squash_vbind : <:xrewrite<
   squash_vbind{| <J> >- e |}
   <-->
   sequent_ind{u, v. happly{v; it}; TermSequent{| <J> >- e |}}
>>

interactive_rw reduce_squash_vbind_nil {| reduce |} : <:xrewrite<
   squash_vbind{| >- e |}
   <-->
   e
>>

interactive_rw reduce_squash_vbind_left {| reduce |} : <:xrewrite<
   squash_vbind{| x: A; <J[x]> >- e[x] |}
   <-->
   squash_vbind{| <J[it]> >- e[it] |}
>>

interactive_rw reduce_squash_vbind_right {| reduce |} : <:xrewrite<
   squash_vbind{| <J>; x: A >- e[x] |}
   <-->
   squash_vbind{| <J> >- e[it] |}
>>

interactive_rw reduce_length_hyp_context {| reduce |} : <:xrewrite<
   length{hyp_context{| <J> >- hyplist{| <K> |} |}}
   <-->
   length{squash_vbind{| <J> >- hyplist{| <K> |} |}}
>>

interactive_rw squash_squash_vbind Perv!bind{x. squash_vbind{| <J['x]> >- 'e |}} : <:xrewrite<
   squash_vbind{| <J[t]> >- e |}
   <-->
   squash_vbind{| <J[it]> >- e |}
>>

interactive squash_vbind_hyplist_wf {| intro |} : <:xrule<
   <H> >- length{squash_vbind{| <J> >- hyplist{| <K> |} |}} in nat
>>

let squash_squash_vbindC = termC (fun t -> squash_squash_vbind (squash_rewrite_arg t))

let resource reduce +=
   [<:xterm< squash_vbind{| <J> >- e |} >>, wrap_reduce squash_squash_vbindC]


interactive_rw reduce_length_squash_hyplist_zero {| reduce |} : <:xrewrite<
   length{squash_vbind{| <J> >- hyplist{||} |}}
   <-->
   0
>>

interactive_rw reduce_length_squash_hyplist_succ {| reduce |} : <:xrewrite<
   length{squash_vbind{| <J> >- hyplist{| <K>; A |} |}}
   <-->
   length{squash_vbind{| <J> >- hyplist{| <K> |} |}} +@ 1
>>

interactive_rw vbind_length_hyp_context Perv!bind{x. vbind{| <J> >- 'e['x] |}} : <:xrewrite<
   vbind{| <J> >- e[length{squash_vbind{| <K> >- hyplist{| <L> |} |}}] |}
   <-->
   vbind{| <J> >- e[length{squash_vbind{| <J>; <K> >- hyplist{| <L> |} |}}] |}
>>

(*
 * Close the lengths.
 *)
let var_x = Lm_symbol.add "x"

let squash_vbind_arg_term = << squash_vbind >>
let squash_vbind_arg_opname = opname_of_term squash_vbind_arg_term
let is_squash_vbind_arg_term = is_no_subterms_term squash_vbind_arg_opname

let is_squash_vbind_term t =
   is_sequent_term t && is_squash_vbind_arg_term (explode_sequent t).sequent_args

let vbind_length_hyp_context_conv t =
   let { sequent_hyps = hyps;
         sequent_concl = concl
       } = explode_sequent t
   in

   (* The variables that are bound here *)
   let bvars =
      SeqHyp.fold (fun bvars _ h ->
            match h with
               Hypothesis (x, _)
             | Context (x, _, _) ->
                  SymbolSet.add bvars x) SymbolSet.empty hyps
   in

   (* Find all the places to be substituted *)
   let is_length_squash_vbind_hyplist t bvars2 =
      if is_length_term t then
         let t = dest_length t in
            is_squash_vbind_term t && SymbolSet.intersectp (SymbolSet.diff (free_vars_set t) bvars2) bvars
      else
         false
   in
   let addrs = find_subterm concl is_length_squash_vbind_hyplist in
   let () =
      if addrs = [] then
         raise (RefineError ("vbind_length_hyp_context_conv", StringTermError ("no matching subterms", t)))
   in

   (* Do the substitutions *)
   let fv = all_vars t in
   let x_v = maybe_new_var_set var_x fv in
   let x = mk_var_term x_v in
   let subst addr =
      let t_x = replace_subterm t addr x in
      let t_bind = mk_bind1_term x_v t_x in
         vbind_length_hyp_context t_bind
   in

   (* Build the conversion *)
   let conv =
      List.fold_left (fun conv addr ->
            subst addr thenC conv) idC addrs
   in
      progressC conv

let vbind_length_hyp_contextC = termC vbind_length_hyp_context_conv

(************************************************************************
 * vbind pushing.
 *)
interactive_rw vbind_vsequent_lof {| normalize_lof |} : <:xrewrite<
   d in nat -->
   n in nat -->
   lof_vbind{| <J> >- sequent_bterm{d<||>; lof_vsequent{arg}{| lof{i. f[i]; n<||>} >- concl |}} |}
   <-->
   sequent_bterm{d +@ length{vlist{| <J> |}}; lof_vsequent{lof_vbind{| <J> >- arg |}}{| lof{i. lof_vbind{| <J> >- f[i] |}; n} >- lof_vbind{| <J> >- concl |} |}}
>>

(*
 * All the action happens during reduction.
 *)
let reduce_vsequent_conv =
   addrC [ClauseAddr 0] (repeatC (vsequent_hyp_term_lof orelseC vsequent_hyp_context_lof))
   thenC vbind_length_hyp_contextC

let reduce_vsequentC =
   progressC (repeatC reduce_vsequent_conv)

let resource reduce_lof +=
   [<:xterm< lof_vbind{| <J> >- lof_vsequent{arg}{| <K> >- concl |} |} >>, reduce_vsequentC]

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
