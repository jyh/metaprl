doc <:doc<
   @spelling{th}

   @module[Itt_struct2]

   The @tt[Itt_struct2] module contains some @emph{derived} rules similar
   to @hrefrule[cut] and @hrefrule[substitution] in the @hrefmodule[Itt_struct] theory.

   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2001-2005 MetaPRL Group, Cornell University and
   California Institute of Technology

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

   Authors: Alexei Kopylov @email{kopylov@cs.caltech.edu}
            Aleksey Nogin @email{nogin@cs.caltech.edu}

   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_equal
extends Itt_struct
extends Itt_squiggle
extends Itt_squash
extends Itt_set
extends Itt_logic
extends Itt_sqsimple
doc docoff

open Lm_debug
open Lm_printf

open Basic_tactics

open Itt_equal
open Itt_struct
open Itt_squiggle
open Itt_dfun
open Itt_sqsimple

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Substitution}

   Using @hrefterm[set] type we can derive more stronger version of the @hrefrule[substitution]
   and @hrefrule[hypSubstitution] rules.
   Suppose we have that $t_1=t_2 @in T$.
   To prove that the substitution $A[t_2]$ for $A[t_1]$ is valid it is necessary to prove that
   the type $A$ is
   functional only for such $x$ @emph{that equals to $t_1$ and $t_2$ in $T$} (not @emph{for all} $x$ as in
   original substitution rules).
>>

interactive substitution2 ('t1 = 't2 in 'T) bind{x. 'C['x]} :
   [equality] sequent { <H> >- 't1 = 't2 in 'T } -->
   [main]  sequent { <H> >- 'C['t2] } -->
   [wf] sequent { <H>; x: 'T; 't1='x in 'T; 't2='x in 'T >- "type"{'C['x]} } -->
   sequent { <H> >- 'C['t1] }

interactive hypSubstitution2 'H ('t1 = 't2 in 'T) bind{y. 'A['y]} :
   [equality] sequent { <H>; x: 'A['t1]; <J['x]> >- 't1 = 't2<|H|> in 'T } -->
   [main] sequent { <H>; x: 'A['t2]; <J['x]> >- 'C['x] } -->
   [wf] sequent { <H>; x: 'A['t1]; <J['x]>; z: 'T; 't1='z in 'T; 't2<|H|> = 'z in 'T
                           >- "type"{'A['z]} } -->
   sequent { <H>; x: 'A['t1]; <J['x]> >- 'C['x] }

doc <:doc<
   A special case of the substitution rule.
>>

interactive substitutionInType ('t_1 = 't_2 in 'T) bind{x. 'c_1='c_2 in 'C['x]} :
   [equality] sequent { <H> >- 't_1 = 't_2 in 'T } -->
   [main]  sequent { <H> >-  'c_1 = 'c_2 in 'C['t_2] } -->
   [wf] sequent { <H>; x: 'T; v: 't_1='x in 'T; w: 't_2='x in 'T
                           >- "type"{'C['x]} } -->
   sequent { <H> >- 'c_1 = 'c_2 in 'C['t_1] }

doc <:doc<
   The @tt{Itt_struct2} module updates the @hreftactic[substT] resource.
   From now @tt[substT] uses the above version of substitution
   instead of original one.
   @docoff
>>

(* substitution *)

let substConclT = argfunT (fun t p ->
   let _, a, _ = dest_equal t in
   let bind = get_bind_from_arg_or_concl_subst p a in
   let tac =
      let v, t = dest_bind1 bind in
         if is_equal_term t &&
            let _, a, b = dest_equal t in
               not (is_var_free v a || is_var_free v b)
         then
            substitutionInType
         else
            substitution2
   in
      tac t bind thenWT thinIfThinningT [-1;-1])

(*
 * Hyp substitution requires a replacement.
 *)
let substHypT i t = funT (fun p ->
   let i = Sequent.get_pos_hyp_num p i in
   let _, a, _ = dest_equal t in
   let bind = get_bind_from_arg_or_hyp_subst p i a in
     if get_thinning_arg p
       then hypSubstitution i t bind
       else hypSubstitution2 i t bind)

let eqSubstT t i = funT (fun p ->
   let tp, a, b = dest_equal t in
      if get_resource_arg p get_sqsimple_resource tp then
         let i = Sequent.get_pos_hyp_num p i in
         let t' = mk_squiggle_term a b in
            assertT t' thenLT [
               sqsimple_sq tp thenLT [autoT thenT addHiddenLabelT "wf"; addHiddenLabelT "equality"];
               hypSubstT (-1) i thenT thinTermT t'
            ]
      else
         if i = 0 then
            substConclT t
         else
            substHypT i t)

let resource subst +=
   equal_term, eqSubstT

doc <:doc<
   @modsubsection{Cut rules}

   There are three advanced versions of the @hrefrule[cut] rule.
   The @tt[cutMem] states that if $s @in S$,
   and $T[x]$ is true for any $x$ from $S$ such that $x=s @in S$,
   then $T[s]$ is certainly true.

>>

interactive cutMem 's 'S bind{x.'T['x]} :
   [assertion] sequent{ <H> >- 's in 'S } -->
   [main]      sequent { <H>; x: 'S; 'x='s in 'S >- 'T['x] } -->
   sequent { <H> >- 'T['s]}

doc <:doc<
   The corresponding tactic is the @tt[letT] tactic.
   This tactic takes a term $x=s @in S$ as an argument
   and a term <<bind{x.'T['x]}>> as an optional with-argument.
   If this argument is omitted then the tactic finds all occurrences of $s$
   in the conclusion and replace them with $x$.

   This tactic is usually used when we have an assumption $s @in S$,
   and want to use the elimination rule corresponding to $S$.

>>

(*
interactive cutEqWeak ('s_1='s_2 in 'S) bind{x.'t['x]} 'v 'u :
   [assertion] sequent{ <H> >- 's_1='s_2 in 'S } -->
   [main]      sequent { <H>; x: 'S; v: 's_1='x in 'S; u: 's_2='x in 'S >- 't['x] in 'T } -->
   sequent { <H> >- 't['s_1] = 't['s_2] in 'T}
*)

interactive cutEq0 ('s_1='s_2 in 'S) bind{x.'t_1['x]  't_2['x]} :
   [assertion] sequent{ <H> >- 's_1='s_2 in 'S } -->
   [main]      sequent { <H>; x: 'S; v: 's_1='x in 'S; u: 's_2='x in 'S >- 't_1['x] = 't_2['x] in 'T } -->
   sequent { <H> >- 't_1['s_1] = 't_2['s_2] in 'T}

doc <:doc<

   The sequent <<sequent{ <H>; x: 'S; <J['x]> >- 't['x] in 'T}>>
   actually means not only that <<'t['x] in 'T>> for any <<'x in 'S>>, but also
   it means @emph{functionality}, i.e. for any two equal elements $s_1$, $s_2$ of $S$
   $t[s_1]$ and $t[s_2]$ should be equal in $T$.

   The following rule states this explicitly.
>>

interactive cutEq ('s_1='s_2 in 'S) bind{x.'t_1['x] = 't_2['x] in 'T['x] } :
   [assertion] sequent{ <H> >- 's_1='s_2 in 'S } -->
   [main]      sequent { <H>; x: 'S; v: 's_1='x in 'S; u: 's_2='x in 'S >- 't_1['x] = 't_2['x] in 'T['x] } -->
   sequent { <H> >- 't_1['s_1] = 't_2['s_2] in 'T['s_1]}


interactive applyFun 'f 'B 'H :
   [wf] sequent { <H>; u:'a = 'b in 'A; <J['u]> >- 'f in 'A -> 'B} -->
   sequent { <H>; u:'a = 'b in 'A; 'f('a)='f('b) in 'B; <J['u]> >- 'C['u]} -->
   sequent { <H>; u:'a = 'b in 'A; <J['u]> >- 'C['u]}


doc <:doc<
   Elimination rule for equalities:
>>
interactive setEqualityElim {| elim [] |} 'H :
   sequent { <H>; 'a = 'b in 'A; squash{'B['a]}; squash{'B['b]}; <J[it]> >- 'C[it] } -->
   sequent { <H>; x: 'a = 'b in { y: 'A | 'B['y] }; <J['x]> >- 'C['x] }

interactive unionEqElimination1 {| elim [] |} 'H :
   sequent { <H>; u: 'x = 'y in 'A; <J[it]> >- 'T[it] } -->
   sequent { <H>; u: inl{'x} = inl{'y} in 'A + 'B; <J['u]> >- 'T['u] }

interactive unionEqElimination2 {| elim [] |} 'H :
   sequent { <H>; u: 'x = 'y in 'B; <J[it]> >- 'T[it] } -->
   sequent { <H>; u: inr{'x} = inr{'y} in 'A + 'B; <J['u]> >- 'T['u] }


(*

interactive productEqElimination {| elim [] |} 'H :
   sequent { <H>; 'x1 = 'x2 in 'A; 'y1= 'y2 in 'B['x1];  <J[it]> >- 'T[it] } -->
   sequent { <H>; u: ('x1,'y1) = ('x2,'y2) in x:'A * 'B['x]; <J['u]> >- 'T['u] }

interactive independentProductEqElimination {| elim [] |} 'H :
   sequent { <H>; 'x1 = 'x2 in 'A; 'y1= 'y2 in 'B;  <J[it]> >- 'T[it] } -->
   sequent { <H>; u: ('x1,'y1) = ('x2,'y2) in 'A * 'B; <J['u]> >- 'T['u] }
*)

doc <:doc<

   The @tt[assertEqT] tactic applies this rule.
   This tactic takes a term $s1=s2 @in S$ as an argument
   and a term <<bind{x.'t['x]}>> as an optional with-argument.
   This tactic helps us to prove an equality from a membership.

>>

doc <:doc<

   The @tt[cutSquash] rule is similar to the @hrefrule[cut] rule.
   If we prove $S$, but do not show the extract term, then we can assert
   $S$ as a @emph{squashed} hypothesis, that is we are not allow to use its extract
   (see @hrefmodule[Itt_squash]).
>>

interactive cutSquash 'H 'S :
   [assertion] sequent { <H>; <J> >- 'S } -->
   [main]      sequent { <H>; x: squash{'S}; <J> >- 'T } -->
   sequent { <H>; <J> >- 'T}

doc <:doc<
   There are two tactics that used this rule: @tt[assertSquashT] and
   @tt[assertSquashAtT].
   They are similar to @hreftactic[assertT] and  @hreftactic[assertAtT].
   The @tt[assertSquashAtT] $n$ $S$ introduces the lemma $S$ after $n$th hypothesis.
   The @tt[assertSquashT] $S$ introduces the lemma $S$ at the end
   of the hypothesis list.

   Next we implement ``third-order'' rewriting using the lambda binding to represent
   arbitrary SO contexts.
>>
interactive fun_sqeq_elim {| elim [ThinOption thinT] |} 'H 'a :
   sequent { <H>; lambda{x. 't1['x]} ~ lambda{x. 't2['x]}; <J>; 't1['a] ~ 't2['a]  >- 'C } -->
   sequent { <H>; lambda{x. 't1['x]} ~ lambda{x. 't2['x]}; <J>  >- 'C }

interactive lambda_sqsubst_concl 'C (lambda{x. 't1['x]} ~ lambda{x.'t2['x]}) 't :
   [equality] sequent { <H> >- lambda{x. 't1['x]} ~ lambda{x. 't2['x]} } -->
   [main] sequent { <H> >- 'C[[ 't2<|H|>['t] ]] } -->
   sequent { <H> >- 'C[[ 't1<|H|>['t] ]] }

interactive lambda_sqsubst_hyp 'H 'C (lambda{x. 't1['x]} ~ lambda{x.'t2['x]}) 't :
   [equality] sequent { <H>; v: 'C[['t1<|H|>['t]]]; <J['v]> >- lambda{x. 't1['x]} ~ lambda{x.'t2['x]} } -->
   [main] sequent { <H>; v: 'C[['t2<|H|>['t]]]; <J['v]> >- 'A['v] } -->
   sequent { <H>; v: 'C[['t1<|H|>['t]]]; <J['v]> >- 'A['v] }

(*
 * XXX: TODO: nogin: The rule I'd actually want is the one below, but so far
 * the combination of type-checker "stupidity" (not knowing that in ITT a
 * subterm of a term of type Term must also have type Term) and rewriter
 * limitations (it can not not match non-sequent contexts that occur more
 * than once in redices) make it impossible to specify this rule.
 *
 * JYH: note that this is not a "stupidity" on the part of the typechecker.
 * The issue is that there is no elimination rule for Term.  It is quite
 * easy for a user to write:
 *
 *    declare foo{'x : Dform} : Term
 *
 * If you wish the invariant to hold, you must provide an elimination rule,
 * and you must restrict what can be declared.
 *
interactive lambda_sqsubst2_concl 'C 'C1 'C2 't1 lambda{x. 'C2[['x 't2]]} bind{x. 't['x]} :
   sequent { <H> >- lambda{x. 'C1[['x 't1]]} ~ lambda{x. 'C2[['x 't2]]} } -->
   sequent { <H> >- 'C[[ 'C2<|H|>[['t<|C;H|>['t2<|C2;H|>] ]] ]] } -->
   sequent { <H> >- 'C[[ 'C1<|H|>[['t<|C;H|>['t1<|C1;H|>] ]] ]] }
 *
 *)

doc docoff

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * General substition.
 *)
let lambdaSqSubstT t i = funT (fun p ->
   let tt = if i = 0 then concl p else nth_hyp p i in
   let x, t1 = dest_lambda (fst (dest_squiggle t)) in
   let arg = ref None in
   let try_match term bvars =
      match !arg with
         Some _ ->
            false
       | None ->
            begin try
               match match_terms [] t1 term with
                  [] ->
                     arg := Some (mk_var_term x);
                     true
                | [v, t] when Lm_symbol.eq v x ->
                     arg := Some t;
                     true
                | _ ->
                     false
            with RefineError _ ->
               false
            end
   in
   let addrs = find_subterm tt try_match in
      match addrs, !arg with
         addr :: _, Some term ->
            if i = 0 then
               lambda_sqsubst_concl addr t term
            else
               lambda_sqsubst_hyp i addr t term
       | _ ->
            raise(RefineError("lambdaSqSubstT", StringTermError ("Nothing appropriate found in", tt))))

let resource subst +=
   << lambda{x.'t1['x]} ~ lambda{y.'t2['y]} >>, lambdaSqSubstT

(* cutMem *)

let letT = argfunT (fun x_is_s_in_S p ->
   let _S, x, s = dest_equal x_is_s_in_S in
   let xname = dest_var x in
   let bind = get_bind_from_arg_or_concl_subst p s in
      cutMem s  _S bind thenMT nameHypT (-2) (string_of_symbol xname) thenMT thinIfThinningT [-1])

let genT s_in_S = funT (fun p ->
   let _S, _, s = dest_equal s_in_S in
   let bind = get_bind_from_arg_or_concl_subst p s in
      cutMem s  _S bind thenMT thinIfThinningT [-1])

(* cutEq *)

let assertEqT =
   let var_z = Lm_symbol.add "z" in
   argfunT (fun eq p ->
      let _, s1, s2 = dest_equal eq in
      let bind =
         try
            get_with_arg p
         with
            RefineError _ ->
               let concl = Sequent.concl p in
               let x = maybe_new_var_set var_z (free_vars_terms [concl; eq]) in
               let t, t1,  t2 = dest_equal concl in
               let t' = var_subst t s1 x in
               let t1' = var_subst t1 s1 x in
               let t2' = var_subst t2 s2 x in
                  <:con< bind{$x$. $mk_equal_term t' t1' t2'$} >>
      in
         if is_xbind_term bind then
            cutEq eq bind thenMT thinIfThinningT [-2;-1]
         else
            raise (RefineError ("assertEqT", StringTermError ("need a \"bind\" term: ", bind))))

(* cutSquash *)

let assertSquashT = cutSquash 0
let assertSquashAtT = cutSquash

(************************************************************************
 * Forward-chaining version.
 *)
doc <:doc<
   In some cases it may also be convenient to reason by forward-chaining.
   Given a hypothesis of the form << lambda{x. 'e1['x]} ~ lambda{x. 'e2['x]} >>,
   rewrite the assumption to wrap the binder << 'x >> in an arbitrary
   expression << 'e['x] >>.

   The general form is currently inexpressible since the rewriter does not
   support context matching.  For the time being, we prove several instances.
>>
interactive lambda_sqequal_elim 'H lambda{x. 'e['x]} :
   sequent { <H>; lambda{x. 'e1['x]} ~ lambda{x. 'e2['x]}; <J>; lambda{x. 'e1['e['x]]} ~ lambda{x. 'e2['e['x]]} >- 'C } -->
   sequent { <H>; lambda{x. 'e1['x]} ~ lambda{x. 'e2['x]}; <J> >- 'C }

interactive lambda_sqequal_elim2 'H lambda{u. lambda{v. 'e3['u; 'v]}} lambda{w. lambda{z. 'e4['w; 'z]}} :
   sequent { <H>; lambda{x. lambda{y. 'e1['x; 'y]}} ~ lambda{x. lambda{y. 'e2['x; 'y]}}; <J>;
      lambda{x. lambda{y. 'e1['e3['x; 'y]; 'e4['x; 'y]]}} ~ lambda{x. lambda{y.'e2['e3['x; 'y]; 'e4['x; 'y]]}} >- 'C } -->
   sequent { <H>; lambda{x. lambda{y. 'e1['x; 'y]}} ~ lambda{x. lambda{y. 'e2['x; 'y]}}; <J> >- 'C }

doc docoff

let x_var = Lm_symbol.add "x"

let lambdaSqElim1T = lambda_sqequal_elim

let lambdaSqElim2T i t =
   let x = maybe_new_var_set x_var (free_vars_set t) in
      lambda_sqequal_elim2 i << lambda{x. lambda{y. 'x}} >> <:con< lambda{$x$. $t$} >>

let lambdaSqElimFull2T = lambda_sqequal_elim2

(************************************************************************
 * lambda-based generalization.
 *)
let genSOVarT = argfunT (fun s p ->
   let t = concl p in
   if not (is_squiggle_term t) then
      raise (RefineError("Itt_subst2.genSOVarT", StringTermError("not a squiggle term", t)));
   let a, b = dest_squiggle t in
   let v = Lm_symbol.add s in
   let v' = maybe_new_var_set v (all_vars t) in
   let t' = mk_var_term v' in
   let expand = ref None in
   let map t =
      if is_so_var_term t then
         let vv, conts, ts = dest_so_var t in
            if Lm_symbol.eq v vv then begin
               begin match ts with
                  [] -> ()
                | [t] ->
                     let x = maybe_new_var (Lm_symbol.add "x") [vv] in
                        expand := Some (mk_apply_term (mk_lambda_term x (mk_so_var_term vv conts [mk_var_term x])) t)
                | _ ->
                     eprintf "Warning: Itt_subst2.genSOVarT: collapse/expand code not fully implemented@."
               end;
               List.fold_left mk_apply_term t' ts
            end else
               t
      else
         t
   in
   let a' = mk_lambda_term v' (map_down map a) in
   let expand, collapse = match !expand with
      None ->
         idT, idT
    | Some t ->
         rwh (foldC t reduce_beta) 0, rwh reduce_beta 0
   in
   let b' = mk_lambda_term v' (map_down map b) in
      assertT (mk_squiggle_term a' b') thenMT
      tryT (expand thenT (hypSubstT (-1) 0 thenT collapse thenT trivialT)))

(*
 * Eta-expand an expression.
 *)
let foldCloseC vars t =
   let t_app =
      let rec gen_lam vars' =
         match vars' with
            [] -> t
          | hd :: tl ->
               let v = Lm_symbol.add hd in
                  mk_lambda_term v (gen_lam tl)
      in
      let rec gen_app vars' f =
         match vars' with
            [] -> f
          | hd :: tl ->
               gen_app tl (mk_apply_term f (mk_var_term (Lm_symbol.add hd)))
      in
         gen_app vars (gen_lam vars)
   in
   let rec justify vars =
      match vars with
         [] ->
            idC
       | _ :: vars ->
            (addrC [Subterm 1] (justify vars)) thenC reduce_beta
   in
   let fold t1 =
      if alpha_equal t1 t then
         foldC t_app (justify vars)
      else
         raise (RefineError ("foldCloseC", StringTermError ("term mismatch", t1)))
   in
      termC fold

(*
 * This is a somewhat more general version of the above.
 * We take a lambda expression and some arguments,
 * and perform an inverse beta-reduction.
 *)
let foldApplyC t =
   (* Apply the lambda to the arguments *)
   let rec apply t args =
      match args with
         [] ->
            t
       | arg :: args ->
            let v, t = dest_lambda t in
            let t = subst1 t v arg in
               apply t args
   in

   (* Collect the arguments from the application *)
   let rec collect args t =
      if is_apply_term t then
         let t, arg = dest_apply t in
            collect (arg :: args) t
      else
         t, args
   in

   (* Get the lambda and the args *)
   let t_lam, args = collect [] t in
   let t_core = apply t_lam args in

   (* Perform the beta-reductions *)
   let rec justify args =
      match args with
         [] ->
            idC
       | _ :: args ->
            (addrC [Subterm 1] (justify args)) thenC reduce_beta
   in

   (* Search and replace *)
   let fold t1 =
      if alpha_equal t1 t_core then
         foldC t (justify args)
      else
         raise (RefineError ("foldApplyC", StringTermError ("term mismatch", t1)))
   in
      termC fold

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
