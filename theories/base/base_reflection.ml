doc <:doc<
   @begin[doc]
   @module[Base_reflection]

   The @tt[Base_reflection] module defines computation over bterms. In
   this module, we formalize the bterm constants and computational
   operations on them by exposing some of the system internals to the user.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 2004 MetaPRL Group

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

   Author: Xin Yu @email{xiny@cs.caltech.edu}
   @end[license]
>>

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>
extends Perv
extends Shell_theory
extends Top_conversionals
doc docoff

open Basic_tactics

open Lm_debug
open Lm_symbol
open Lm_printf

open Term_sig
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermType
open Refiner.Refiner.TermMan
open Refiner.Refiner.Rewrite
open Refiner.Refiner.RefineError
open Dform
open Lm_rformat

(************************************************************************
 * List utilities.
 *)

(*
 * Lists.
 *)
let rnil_term = << rnil >>
let rnil_opname = opname_of_term rnil_term
let is_rnil_term = alpha_equal rnil_term

let rcons_term = << rcons{'a; 'b} >>
let rcons_opname = opname_of_term rcons_term

let is_rcons_term = is_dep0_dep0_term rcons_opname
let mk_rcons_term = mk_dep0_dep0_term rcons_opname
let dest_rcons = dest_dep0_dep0_term rcons_opname

let rec is_rlist_term t =
   is_rnil_term t || (is_rcons_term t && is_rlist_term (snd (dest_rcons t)))

let rec dest_rlist t =
   if is_rnil_term t then
      []
   else
      let hd, tl = dest_rcons t in
         hd :: (dest_rlist tl)

let rec mk_rlist_term = function
   h::t ->
      mk_rcons_term h (mk_rlist_term t)
 | [] ->
      rnil_term

doc <:doc< @begin[doc]
   @modsection{Bterm}

   We use sequents for representing bterms internally. The internal
   representation for $bterm@{x_1,@ldots,x_n.t[@vec{x}]@}$ is
   $x_1:@_; @~@ldots; @~x_n:@_ @~@vdash_{bterm}@~t[@vec{x}]$, where
   $n @ge 0$, << 't >> is constructed from quoted operators, and
   $x_i$ and $@_$ can be anything. The sequent contexts represent
   meta-variables that denote arbitrary sequences of bterm bindings.
   For example, $bterm@{<<Gamma>>,x,<<Delta>>.x@}$ is a schema for an
   arbitrary bterm variable.
@end[doc] >>

declare typeclass BtermType -> Term
declare sequent [bterm] { Quote : BtermType >- Quote } : Term
declare term : BtermType

doc docoff

let bterm_arg = <<bterm>>

let hyp_of_var v =
   Hypothesis(v, <<term>>)

let get_var = function
   Hypothesis (v, term) -> v
 | Context (v, conts, subterms) ->
      raise (Invalid_argument "Base_reflection.get_bterm_var: bterm cannot have contexts as hypotheses")

let make_bterm_sequent hyps concl =
   mk_sequent_term {
      sequent_args = bterm_arg;
      sequent_hyps = SeqHyp.of_list hyps;
      sequent_concl = concl
   }

let dest_bterm_sequent term =
   let seq = TermMan.explode_sequent term in
      if alpha_equal seq.sequent_args bterm_arg then
         SeqHyp.to_list seq.sequent_hyps, seq.sequent_concl
      else raise (RefineError ("dest_bterm_sequent", StringTermError ("not a bterm sequent", term)))

let dest_bterm_sequent_and_rename term vars =
   let seq = TermMan.explode_sequent_and_rename term vars in
      if alpha_equal seq.sequent_args bterm_arg then
         SeqHyp.to_list seq.sequent_hyps, seq.sequent_concl
      else raise (RefineError ("dest_bterm_sequent_and_rename", StringTermError ("not a bterm sequent", term)))

doc <:doc< @begin[doc]
   @modsection{Computational Operations on Bterms}
   @modsubsection{@tt[If_quoted_op]}

   << if_quoted_op{'op; 'tt} >> evaluates to << 'tt >> when << 'op >> is a
   quoted bterm operator and must fail to evaluate otherwise.
@end[doc] >>

declare if_quoted_op{'op; 'tt}

doc <:doc<
   @begin[doc]
   << fake_mlrw[reduce_if_quoted_op]{
         if_quoted_op{bterm{|<H> >-
            <:doc<@underline{<<'op>>}@{
               <<df_context{'J_1<|H|>}>>.<< 't_1<|H|> >>, @ldots,
               <<df_context{'J_n<|H|>}>>.<< 't_n<|H|> >>@}>>|}; 'tt};
         'tt} >>
   @end[doc]
   @docoff
>>
ml_rw reduce_if_quoted_op {| reduce |} : ('goal :  if_quoted_op{ bterm{| <H> >- 't |}; 'tt }) =
   let bt, tt = two_subterms goal in
   let hyps, t = dest_bterm_sequent bt in
   let t' = unquote_term t in
      tt

(*************************************************************************
 * if_bterm{'bt; 'tt} evaluates to 'tt when 'bt is a well-formed bterm
 * operator and must fail to evaluate otherwise.
 *
 * rewrite axiom: if_bterm{bterm{<H>; x:_; <J> >- x}; 'tt} <--> 'tt
 * ML rewrite axiom:
 *    if_bterm{bterm{<H> >- _op_{<J1>.t1, ..., <Jn>.tn}}; 'tt}
 *       <-->
 *    if_bterm{bterm{<H>; <J1> >- 't1};
 *       if_bterm{bterm{<H>; <J2> >- 't2};
 *          ...
 *            if_bterm{bterm{<H>; <Jn> >- 'tn}; 'tt}...}}
 *)

doc <:doc< @begin[doc]
   @modsubsection{If_bterm}

   << if_bterm{'bt; 'tt} >> evaluates to << 'tt >> when << 'bt >> is a
   well-formed bterm operator and must fail to evaluate otherwise.
@end[doc] >>

declare if_bterm{'bt; 'tt}

prim_rw reduce_ifbterm1 'H :
   if_bterm{ bterm{| <H>; x: term; <J> >- 'x |}; 'tt } <--> 'tt

doc <:doc<
   @begin[doc]
   << fake_mlrw[reduce_ifbterm2]{
         if_bterm{bterm{|<H> >-
            <:doc<@underline{<<'op>>}@{
               <<df_context{'J_1<|H|>}>>.<< 't_1<|H|> >>, @ldots,
               <<df_context{'J_n<|H|>}>>.<< 't_n<|H|> >>@}>>|}; 'tt};
         <:doc<if_bterm{bterm{|<H>; <J_1> >- 't_1|};
         @~@~@~ if_bterm{bterm{|<H>; <J_2> >- 't_2|};
         @~@~@~@~@~@~ @ldots
         @~@~@~@~@~@~@~@~@~ <<if_bterm{bterm{|<H>; <J_n> >- 't_n|}; 'tt}>> @ldots }} >>} >>
   @end[doc]
   @docoff
>>

ml_rw reduce_ifbterm2 : ('goal :  if_bterm{ bterm{| <H> >- 't |}; 'tt }) =
   let bt, tt = two_subterms goal in
   let hyps, t = dest_bterm_sequent bt in
   let t' = dest_term (unquote_term t) in
   let rec wrap_if = function
      [] -> tt
    | s :: subterms ->
         let bt = dest_bterm s in
         let new_bterm = make_bterm_sequent (hyps @ (List.map hyp_of_var bt.bvars)) bt.bterm in
            <:con<if_bterm{$new_bterm$;$wrap_if subterms$}>>
   in wrap_if t'.term_terms

let rec onSomeHypC rw = function
   1 -> rw 1
 | i when i > 0 -> rw i orelseC (onSomeHypC rw (i - 1))
 | _ -> failC

let reduce_ifbterm =
   termC (fun goal ->
      let t,tt =  two_subterms goal in
      let seq = TermMan.explode_sequent  t in
      let concl = seq.sequent_concl in
         if is_quoted_term concl then reduce_ifbterm2
         else if is_var_term concl then onSomeHypC reduce_ifbterm1 (SeqHyp.length seq.sequent_hyps)
         else failC)

let resource reduce +=
   (<< if_bterm{ bterm{| <H> >- 't |}; 'tt } >>, reduce_ifbterm)

(***************************************************************************
 * subterms{'bt} returns a list of sub-bterms of 'bt, undefined if 'bt
 * is not a well-formed bterm
 *
 * rewrite axiom: subterms{bterm{<H>; x:_; <J> >- x}} <--> []
 * ML rewrite_axiom:
 *    subterms{bterm{<H> >- _op_{<J1>.t1, ..., <Jn>.tn}}}
 *       <-->
 *    [ bterm{<H>; <J1> >- t1}; ...; bterm{<H>; <Jn> >- tn} ]
 *)

doc <:doc< @begin[doc]
   @modsubsection{Subterms}

   << subterms{'bt} >> returns a list of sub-bterms of << 'bt >>, undefined
   if << 'bt >> is not a well-formed bterm.
@end[doc] >>

declare subterms{'bt}

prim_rw reduce_subterms1 'H :
   subterms{ bterm{| <H>; x: term; <J> >- 'x |} } <--> rnil

doc <:doc<
   @begin[doc]
   << fake_mlrw[reduce_subterms2]{
         subterms{bterm{|<H> >-
            <:doc<@underline{<<'op>>}@{
               <<df_context{'J_1<|H|>}>>.<< 't_1<|H|> >>, @ldots,
               <<df_context{'J_n<|H|>}>>.<< 't_n<|H|> >>@}>>|}};
         <:doc<[<<bterm{|<H>; <J_1> >- 't_1|}>>; @ldots; <<bterm{|<H>; <J_n> >- 't_n|}>> ] >>} >>
   @end[doc]
   @docoff
>>

ml_rw reduce_subterms2 {| reduce |} : ('goal :  subterms{ bterm{| <H> >- 't |} }) =
   let bt = one_subterm goal in
   let hyps, t = dest_bterm_sequent bt in
   let t' = dest_term (unquote_term t) in
   let wrap s =
      let bt = dest_bterm s in
      	make_bterm_sequent (hyps @ (List.map hyp_of_var bt.bvars)) bt.bterm
   in
      mk_rlist_term (List.map wrap t'.term_terms)

let reduce_subterms =
   termC (fun goal ->
      let bt =  one_subterm goal in
      let seq = TermMan.explode_sequent bt in
      let concl = seq.sequent_concl in
         if is_quoted_term concl then reduce_subterms2
         else if is_var_term concl then onSomeHypC reduce_subterms1 (SeqHyp.length seq.sequent_hyps)
         else failC)

let resource reduce +=
   (<< subterms{ bterm{| <H> >- 't |} } >>, reduce_subterms)

(************************************************************************
 * make_bterm{'bt; 'btl} takes the top-level operator of 'bt and
 * replaces the subterms with the ones in 'btl (provided they have a
 * correct arity).
 *
 * rewrite axiom: make_bterm{bterm{<H>; x:_; <J> >- x}; []} <--> bterm{<H>; x:_; <J> >- x}
 * ML rewrite_axiom:
 *     make_bterm{bterm{<H> >- _op_{<J1>.r1, ..., <Jn>.rn}}};
 *        [bterm{<H>; <J1> >- t1}; ...; bterm{<H>; <Jn> >- tn}] }
 *     <-->
 *     bterm{<H> >- _op_{<J1>.t1, ..., <Jn>.tn}}
 *
 * (ri's are ignored).
 *)

doc <:doc< @begin[doc]
   @modsubsection{Make_bterm}

   << make_bterm{'bt; 'btl} >> takes the top-level operator of << 'bt >>
   and replaces the subterms with the ones in << 'btl >> (provided they
   have a correct arity).
@end[doc] >>

declare make_bterm{'bt; 'bt1}

prim_rw reduce_make_bterm1 'H :
   make_bterm{ bterm{| <H>; x: term; <J> >- 'x |}; rnil } <--> bterm{| <H>; x: term; <J> >- 'x |}

doc <:doc<
   @begin[doc]
   << fake_mlrw[reduce_make_bterm2]{
         make_bterm{bterm{|<H> >-
            <:doc<@underline{<<'op>>}@{
               <<df_context{'J_1<|H|>}>>.<< 'r_1<|H|> >>, @ldots,
               <<df_context{'J_n<|H|>}>>.<< 'r_n<|H|> >>@}>>|};
               <:doc< [<<bterm{| <H>; <J_1> >- 't_1|}>>; @ldots; <<bterm{|<H>; <J_n> >- 't_n|}>>]>> };
         bterm{|<H> >-
            <:doc<@underline{<<'op>>}@{
               <<df_context{'J_1<|H|>}>>.<< 't_1<|H|> >>, @ldots,
               <<df_context{'J_n<|H|>}>>.<< 't_n<|H|> >>@}>>|} } >>
   @end[doc]
   @docoff
>>

let rec make_bterm_aux lista listb fvars hvar lenh =
   match lista, listb with
      [], [] -> []
    | a1 :: a, b1:: b ->
         let b1h, b1g = dest_bterm_sequent_and_rename b1 fvars in
            if (List.length b1h - a1 = lenh) then
               let hvar', j1' = Lm_list_util.split lenh (List.map get_var b1h) in
               let b1g' = subst b1g hvar' (List.map mk_var_term hvar) in
                  (mk_bterm j1' b1g') :: (make_bterm_aux a b fvars hvar lenh)
            else raise (Invalid_argument "Base_reflection.make_bterm_aux: unmatched arity.")
    | _, _ -> raise (Invalid_argument "Base_reflection.make_bterm_aux: unmatched arity.")

ml_rw reduce_make_bterm2 : ('goal :  make_bterm{ 'bt; 'bt1 }) =
   let bt, bt1 = two_subterms goal in
   let fvars = free_vars_set bt1 in
   let hyps1, t = dest_bterm_sequent_and_rename bt fvars in
   let t' = dest_term (unquote_term t) in
   let bt1' = dest_rlist bt1 in
      if (List.length t'.term_terms = (List.length bt1')) then
               let lenJr_list = List.map (fun tmp -> List.length (dest_bterm tmp).bvars) t'.term_terms in
               let lenh = List.length hyps1 in
               let hvar = List.map get_var hyps1 in
               let fvars = SymbolSet.add_list fvars hvar in
               let terms = make_bterm_aux lenJr_list bt1' fvars hvar lenh in
                        make_bterm_sequent (List.map hyp_of_var hvar) (quote_term (mk_term t'.term_op terms))
      else  raise (RefineError ("reduce_make_bterm2", StringError "unmatched arities"))

let reduce_make_bterm =
   termC (fun goal ->
      let bt, btl =  two_subterms goal in
      let seq = TermMan.explode_sequent  bt in
      let concl = seq.sequent_concl in
         if is_quoted_term concl then reduce_make_bterm2
         else if is_var_term concl then onSomeHypC reduce_make_bterm1 (SeqHyp.length seq.sequent_hyps)
         else failC)

let resource reduce +=
   (<< make_bterm{ bterm{| <H> >- 't|}; 'btl } >>, reduce_make_bterm)

(**************************************************************************
 * if_same_op{'bt1; 'bt2; 'tt; 'ff} evaluates to 'tt if 'bt1 and 'bt2
 * are two well-formed bterms with the same top-level operator (including
 * all the params and all the arities) and to 'ff when operators are
 * distinct. Undefined if either 'bt1 or 'bt2 is ill-formed.
 *)

doc <:doc< @begin[doc]
   @modsubsection{@tt[If_same_op]}

   << if_same_op{'bt1; 'bt2; 'tt; 'ff} >> evaluates to << 'tt >> if << 'bt1 >>
   and << 'bt2 >> are two well-formed bterms with the same top-level operator
   (including all the parameters and all the arities) and to << 'ff >> when
   operators are distinct. Undefined if either << 'bt1 >> or << 'bt2 >> is
   ill-formed.
   @end[doc]
>>

declare if_same_op{'bt1; 'bt2; 'tt; 'ff}

doc docoff
ml_rw reduce_if_same_op {| reduce |} : ('goal :  if_same_op{ 'bt1; 'bt2; 'tt; 'ff } ) =
   let bt1, bt2, tt, ff = four_subterms goal in
   let hyps1, g1 = dest_bterm_sequent bt1 in
   let hyps2, g2 = dest_bterm_sequent bt2 in
   let t1 = dest_term (unquote_term g1) in
   let t2 = dest_term (unquote_term g2) in
   let bvar_len t = List.length (dest_bterm t).bvars in
      if    ops_eq t1.term_op t2.term_op
         && List.length t1.term_terms = List.length t2.term_terms
         && List.map bvar_len t1.term_terms = List.map bvar_len t1.term_terms
      then  tt
      else  ff

(**************************************************************************
 * if_simple_bterm{'bt; 'tt; 'ff} evaluates to 'tt when 'bt has
 * 0 bound variables, to 'ff when it is a bterm with non-0 bound
 * variables and is undefined otherwise.
 *
 * rewrite axiom: if_simple_bterm{bterm{x:_; <H> >- 't['x]}; 'tt; 'ff} <--> 'ff
 *                if_simple_bterm{bterm{ >- 't}; 'tt; 'ff} <--> 'tt
 *)

doc <:doc< @begin[doc]
   @modsubsection{If_simple_bterm}

   << if_simple_bterm{'bt; 'tt; 'ff} >> evaluates to << 'tt >> when << 'bt >>
   has $0$ bound variables, to << 'ff >> when it is a bterm with non-$0$ bound
   variables and is undefined otherwise.
   @end[doc]
>>

declare if_simple_bterm{'bt; 'tt; 'ff}

prim_rw reduce_if_simple_bterm1 {| reduce |} :
   if_simple_bterm{ bterm {| x: term; <H> >- 't['x] |}; 'tt; 'ff } <--> 'ff

prim_rw reduce_if_simple_bterm2 {| reduce |} :
   if_simple_bterm{ bterm {| >- 't |}; 'tt; 'ff } <--> 'tt

doc docoff
let reduce_if_simple_bterm =
   termC (fun goal ->
      let t, tt, ff =  three_subterms goal in
      let seq = TermMan.explode_sequent  t in
         if SeqHyp.length seq.sequent_hyps = 0 then reduce_if_simple_bterm2
         else reduce_if_simple_bterm1)

let resource reduce +=
   (<< if_simple_bterm{ bterm{| <H> >- 't|}; 'tt; 'ff } >>, reduce_if_simple_bterm)

(*************************************************************************
 * if_var_bterm{'bt; 'tt; 'ff} evaluates to 'tt when 'bt is a
 * well-formed bterm with a bound variable body, to 'ff when it is a bterm
 * with a non-variable top-level operator.
 *
 * rewrite axiom:
 *     if_var_bterm{bterm{<H>; x:_; <J> >- 'x}; 'tt; 'ff} <--> 'tt
 * ML rewrite axiom:
 *     if_var_bterm{bterm{<H> >- _op_{...}}; 'tt; 'ff} <--> 'ff
 *)

doc <:doc< @begin[doc]
   @modsubsection{@tt[If_var_bterm]}

   << if_var_bterm{'bt; 'tt; 'ff} >> evaluates to << 'tt >> when << 'bt >>
   is a well-formed bterm with a bound variable body, to << 'ff >> when
   it is a bterm with a non-variable top-level operator.
@end[doc] >>

declare if_var_bterm{'bt; 'tt; 'ff}

prim_rw reduce_if_var_bterm1 'H :
   if_var_bterm{ bterm{| <H>; x: term; <J> >- 'x |}; 'tt; 'ff } <--> 'tt

doc <:doc<
   @begin[doc]
   << fake_mlrw[reduce_if_var_bterm2]{
         if_var_bterm{bterm{|<H> >-
            <:doc<@underline{<<'op>>}@{@ldots@}>>|}; 'tt; 'ff};
         'ff (*<:doc< << 'ff >> >>*)} >>
   @end[doc]
   @docoff
>>
ml_rw reduce_if_var_bterm2 : ('goal :  if_var_bterm{ bterm{| <H> >- 't |}; 'tt; 'ff }) =
   let bt, tt, ff = three_subterms goal in
   let hyps, t = dest_bterm_sequent bt in
      if is_quoted_term t  then ff
      else raise (RefineError ("reduce_if_var_bterm2", StringTermError ("not a quoted term", t)))

let reduce_if_var_bterm =
   termC (fun goal ->
      let t, tt, ff =  three_subterms goal in
      let seq = TermMan.explode_sequent  t in
      let concl = seq.sequent_concl in
         if is_quoted_term concl then reduce_if_var_bterm2
         else if is_var_term concl then onSomeHypC reduce_if_var_bterm1 (SeqHyp.length seq.sequent_hyps)
         else failC)

let resource reduce +=
   (<< if_var_bterm{ bterm{| <H> >- 't|}; 'tt; 'ff } >>, reduce_if_var_bterm)

(************************************************************************
 * subst{'bt; 't} substitutes 't for the first bound variable of 'bt.
 *
 * rewrite_axiom:
 * subst{bterm{x:_; <H> >- 't1['x]}; bterm{ >- 't2}} <-->
 * bterm{<H> >- 't1['t2] }
 *)

doc <:doc< @begin[doc]
   @modsubsection{Substitution}

   << subst{'bt; 't} >> substitutes << 't >> for the first bound variable
   of << 'bt >>.
   @end[doc]
>>

declare subst{'bt; 't}

prim_rw reduce_subst {| reduce |} :
   subst{ bterm{| x: term; <H> >- 't1['x] |}; bterm{| >- 't2 |} } <-->
      bterm{| <H> >- 't1['t2] |}

doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform term_df : except_mode[src] :: term =
   `"_"

declare sequent[display_bterm] { Quote : Dform >- Quote } : Dform
declare sequent[bterm_sep] { Quote : Dform >- Quote } : Dform

dform bterm_df : parens :: bterm{| <H> >- 't |} =
   slot{display_bterm{| <H> >- 't |}}

dform bterm_cont_df : display_bterm{| df_context{'c}; <H> >- 't |} =
   df_context{'c} bterm_sep{| <H> >- 't |} display_bterm{| <H> >- 't |}

dform bterm_var_df : display_bterm{| v: term; <H> >- 't |} =
   'v bterm_sep{| <H> >- 't |} display_bterm{| <H> >- 't |}

dform bterm_unusual_df : display_bterm{| v: 't1; <H> >- 't |} =
   'v `":" slot{'t1} bterm_sep{| <H> >- 't |} display_bterm{| <H> >- 't |}

dform bterm_nil_df : display_bterm{| >- 't |} =
   `"." slot{'t}

dform bterm_sep_cons_df : bterm_sep{| 't1; <H> >- 't |} = `","
dform bterm_sep_nil_df : bterm_sep{| >- 't |} = `""

dform if_quoted_op_df : if_quoted_op{'bt; 'tt} =
   pushm[3] `"if_quoted_op(" slot{'bt} `";" space slot{'tt} `")" popm
dform if_bterm_df : if_bterm{'bt; 'tt} =
   pushm[3] `"if_bterm(" slot{'bt} `";" space slot{'tt} `")" popm
dform subterms_df : except_mode[src] :: subterms{'bt} =
   `"subterms(" slot{'bt} `")"
dform make_bterm_df : make_bterm{'bt; 'btl} =
   pushm[3] `"make_bterm(" slot{'bt} `";" space slot{'btl} `")" popm
dform if_same_op_df : if_same_op{'bt1; 'bt2; 'tt; 'ff} =
   szone pushm[3] `"if_same_op(" slot{'bt1} `";" hspace slot{'bt2} `";" hspace slot{'tt} `";" hspace slot{'ff} `")" popm ezone
dform if_simple_bterm_df : if_simple_bterm{'bt; 'tt; 'ff} =
   szone pushm[3] `"if_simple_bterm(" slot{'bt} `";" hspace slot{'tt} `";" hspace slot{'ff} `")" popm ezone
dform if_var_bterm_df : if_var_bterm{'bt; 'tt; 'ff} =
   szone pushm[3] `"if_var_bterm(" slot{'bt} `";" hspace slot{'tt} `";" hspace slot{'ff} `")" popm ezone
dform subst_df : subst{'bt; 't} =
   `"subst(" slot{'bt} `"; " slot{'t} `")"
