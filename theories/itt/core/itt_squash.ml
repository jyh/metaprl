doc <:doc<
   @spelling{th unsquash unsquashed}
   @module[Itt_squash]

   The @tt[Itt_squash] module defines a @i[squash] type.
   <<squash{'A}>> hides computational content of $A$.
   <<squash{'A}>> is inhabited @emph{iff} $A$ is inhabited.
   When inhabited, <<squash{'A}>> contains only one element $@it$.
   That is <<squash{'A}>> means that $A$ is true, but we do not know its
   computational content.
   Consequentially,  the sequent
   $$<<sequent{ <H>; x: squash{'A}; <J> >- 'C}>>$$
   is true when $C$ is true (with the assumption that $A$ is true),
   but extract of $C$ does not depend on the witness of $A$.
   Note that $x$ in this sequent stands not for a witness for $A$,
   but just for $@it$.

   Squash types are needed to define set in @hrefmodule[Itt_set]. Also,
   it can be argued (see @cite[KN01]) that it is consistent to use
   @emph{classical} reasoning under @tt[squash] without losing
   constructive content.

   The @tt[Itt_squash] module also defines a resource that can be used to
   help prove ``squash'' stability---that is, to infer the proof
   of a proposition given an assumption that it is true.

   This module defines a generic resource @hrefresource[squash_resource] that
   can be used to recover computational content from a @tt[squash] proof.
   Additions to the resource are done through resource annotations, see the
   @hrefresource[squash_resource] section for more information. Tactics
   @hreftactic[squashT] and @hreftactic[unsquashT]
   make use of the @hrefresource[squash_resource].

   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1997-2006 MetaPRL Group, Cornell University and
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

   Authors:
     Jason Hickey @email{jyh@cs.caltech.edu}
     Alexei Kopylov @email{kopylov@cs.caltech.edu}
     Aleksey Nogin @email{nogin@cs.caltech.edu}

   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_equal
extends Itt_struct
doc docoff

open Lm_debug
open Lm_printf
open Term_stable

open Basic_tactics

open Itt_struct
open Itt_equal

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @terms

   The @tt[squash] term defines the @tt[squash] type.
>>
declare squash{'A}
doc docoff

let squash_term = << squash{'a} >>
let squash_opname = opname_of_term squash_term
let is_squash_term = is_dep0_term squash_opname
let dest_squash = dest_dep0_term squash_opname
let mk_squash_term = mk_dep0_term squash_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform squash_df : except_mode[src] :: squash{'A} = math_squash{'A}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Equality and typehood}

   <<squash{'A}>> is a type if $A$ is a type.
>>
prim squashEquality {| intro [] |}  :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   sequent { <H> >- squash{'A1} = squash{'A2} in univ[i:l] } = it

prim squashType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- "type"{squash{'A}} } =
   it

doc <:doc<
   @modsubsection{Introduction}

   A squashed type <<squash{'A}>> is true if $A$ is true.
   This rule is irreversible, so we use @tt[AutoMustComplete] to prevent
   @hreftactic[autoT] from using it too eagerly.
>>
prim squashMemberFormation {| intro [AutoMustComplete]; nth_hyp |} :
   sequent { <H> >- 'A } -->
   sequent { <H> >- squash{'A} } =
   it

doc <:doc<
   @modsubsection{Elimination}

   The first rule, @tt[unsquashEqual], allows equalities to
   be unsquashed (because the proof can always be inferred).
   The second rule, @tt[squashElim] shows that $@it$ is the only element
   of a non-empty squashed type.
>>
prim unsquashEqualWeak 'H :
   sequent { <H>; 'P; <J> >- 'x = 'y in 'A } -->
   sequent { <H>; squash{'P}; <J> >- 'x = 'y in 'A } =
   it

prim squashElim 'H :
   ('t['u] : sequent { <H>; u: squash{'P}; <J[it]> >- 'C[it] }) -->
   sequent { <H>; u: squash{'P}; <J['u]> >- 'C['u] } =
   't[it]

doc docoff

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (squash_term,  Typeinf.infer_map dest_squash)

(************************************************************************
 * THEOREMS                                                             *
 ************************************************************************)

doc <:doc<
   @modsection{Derived Rules}

   First, we can prove a stronger version of @tt[unsquashEqualWeak] by
   combining it with @tt[squashElim].
>>
interactive unsquashEqual 'H :
   sequent { <H>; 'P; <J[it]> >- 'x[it] = 'y[it] in 'A[it] } -->
   sequent { <H>; u: squash{'P}; <J['u]> >- 'x['u] = 'y['u] in 'A['u] }

doc docoff
interactive unsquashWWitness 'H 't:
   sequent { <H>; 'P; <J[it]> >- 't in 'A[it] } -->
   sequent { <H>; u: squash{'P}; <J['u]> >- 'A['u] }

doc <:doc<
   Next, we show that a witness of a provable hidden type is $@it$.
>>
interactive squashMemberEquality {| intro [] |} :
   [wf] sequent { <H> >- squash{'A} } -->
   sequent { <H> >- it in squash{'A} }

doc <:doc<
   The @tt[squashStable] rule establishes that we can unsquash a proposition
   when it is possible to recover its witness from simply knowing the proposition
   to be true.
>>
interactive squashStable 't :
   sequent { <H> >- squash{'A} } -->
   [aux] sequent { <H>; 'A >- 't in 'A } -->
   sequent { <H> >- 'A}

interactive unsquashHypEqual 'H :
   sequent { <H>; 'x = 'y in 'A; <J[it]> >- 'C[it] } -->
   sequent { <H>; u: squash{('x = 'y in 'A)}; <J['u]> >- 'C['u] }

interactive unsquash 'H :
   sequent { <H>; 'P; <J[it]> >- squash{'T[it]} } -->
   sequent { <H>; u: squash{'P}; <J['u]> >- squash{'T['u]} }

doc docoff
interactive unsquashStableGoal 'H :
   sequent { <H>; 'A; <J[it]> >- 'C[it] } -->
   [aux] sequent { <H>; u: squash{'A}; <J['u]>; squash{'C['u]} >- 'C['u] } -->
   sequent { <H>; u: squash{'A}; <J['u]> >- 'C['u]}

interactive unsquashHypGoalStable 'H :
   sequent { <H>; 'A; <J[it]> >- 'C[it] } -->
   [aux] sequent { <H>; u: squash{'A}; <J['u]> >- 'A } -->
   sequent { <H>; u: squash{'A}; <J['u]> >- 'C['u]}

interactive unsquashStable 'H 't :
   sequent { <H>; 'A; <J[it]> >- 'C[it] } -->
   [aux] sequent { <H>; u: squash{'A}; <J['u]>; 'A >- 't in 'A } -->
   sequent { <H>; u: squash{'A}; <J['u]> >- 'C['u]}

interactive squashAssert 'A :
   sequent { <H> >- squash{'A} } -->
   [assertion] sequent { <H>; squash{'A} >- 'C } -->
   sequent { <H> >- 'C }

interactive assertSquash :
   [sqstable] sequent { <H>;  squash{'C} >- 'C } -->
   sequent { <H> >- squash{'C} } -->
   sequent { <H> >- 'C }

(*
 * H >- Ui ext squash(A)
 * by squashFormation
 * H >- Ui ext A
 *)
interactive squashFormation :
   sequent { <H> >- univ[i:l] } -->
   sequent { <H> >- univ[i:l] }

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

doc <:doc<
   @resources

   The @Comment!resource[squash_resource] keeps 4 kind of tactics, as described by the
   @tt[squash_info] type. The $@tt[SqUnsquash](T,@i[tac])$ is used when @i["tac i"]
   is capable turning @i{i}-th hypothesis from $@squash{T}$ into $T$.
   The $@tt[SqStable](T,t,@i[tac])$ variant is used when @i[tac] is capable
   of proving <<sequent{ <H> >- 't in 'T}>> from <<sequent{ <H> >- 'T}>>. Third,
   the $@tt[SqUnsquashGoal](T,@i[tac])$ is used when @i["tac i"] can unsquash
   @i{i}-th hypothesis provided the conclusion of the sequent is $T$. Finally,
   $@tt[SqStableGoal](T,@i[tac])$ is used when @i[tac] can prove $T$ from
   $@squash{T}$.

   The only way to improve the @tt{squash_resource} outside of the
   @tt{Itt_squash} theory is to use @it{resource annotations}. Currently, the
   following kinds of rules are recognized by the @tt{squash_resource} annotations:
   $<<sequent{ <H> >- squash{'A}}>>@space<<longrightarrow>>@space<<sequent{ <H> >- 'A}>>$,
   $<<sequent{ <H> >- 'A}>>@space<<longrightarrow>>@space<<sequent{ <H> >- 't in 'A}>>$,
   <<sequent{ <H> >- 't in 'A}>> and <<sequent{ <H>; x: 'A; <J['x]> >- 'C['x]}>>
   (e.g $A$ is a falsity), although it is possible
   to add support for other kinds of rules if necessary.

   The squash resource represents data using a shape table.
   @docoff
>>
type squash_inf =
   SqUnsquash of (int -> tactic)
 | SqStable of term * tactic
 | SqUnsquashGoal of (int -> tactic)
 | SqStableGoal of tactic

type squash_info = term * squash_inf
type squash_out = (int -> tactic) * (term -> bool)

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Extract an SQUASH tactic from the data.
 *)
let unsq_err = RefineError("Itt_squash.unsquashT", StringError ("squashMemberFormation while in autoT"))
let unsquash_tactic tbl = 
   argfunT (fun i p ->
      let conc = concl p in
      if i = 0 then
         if (slookup_all tbl (one_subterm conc) = []) && (d_in_auto p) then
            raise unsq_err
         else
            squashMemberFormation
      else
         let hyp = dest_squash (nth_hyp p i) in
         match slookup_all tbl conc, slookup_all tbl hyp with
            ((SqUnsquashGoal tac :: _)|(_ :: SqUnsquashGoal tac :: _)|(_ :: _ :: SqUnsquashGoal tac :: _)), _
          | _, ((SqUnsquash tac :: _)|(_ :: SqUnsquash tac :: _)|(_ :: _ :: SqUnsquash tac :: _)) ->
               tac i
          | (SqStable (t,tac) :: _), _ ->
               unsquashWWitness i t thenT tac
          | (SqStableGoal tac :: _), _ ->
               tac thenT unsquash i thenT squashMemberFormation
          | _, (SqStable (t,tac) :: _) ->
               unsquashStable i t thenLT [ idT; tac thenT trivialT]
          | _, (SqUnsquashGoal tac :: _) ->
               unsquashHypGoalStable i thenLT [idT; tac i thenT trivialT]
          | (SqUnsquash tac :: _), _ ->
               unsquashStableGoal i thenLT [idT; tac (-1) thenT hypothesis (-1)]
          | _, (SqStableGoal tac :: _) ->
               unsquashStableGoal i thenLT [idT; tac thenT hypothesis (-1)]
          | [], [] ->
               raise (RefineError ("squash", StringTermError ("squash tactic doesn't know about ",
                  mk_xlist_term [hyp;<<slot[" |- "]>>;conc])))),
   (fun t -> (slookup_all tbl t) <> [])

let process_squash_resource_annotation ?labels name contexts args stmt loc tac =
   if contexts.spec_addrs <> [||] then
      raise (Invalid_argument ((string_of_loc loc) ^ ": squash_stable resource annotation:
" ^ name ^ ": contexts (address) arguments are not supported yet"));
   rule_labels_not_allowed loc labels;
   let assums, goal = unzip_mfunction stmt in
   let egoal = TermMan.explode_sequent goal in
   let concl = egoal.sequent_concl in
   match contexts.spec_ints, args, assums, (SeqHyp.to_list egoal.sequent_hyps) with
      (* H |- [T] --> H |- T *)
      [||], [], [_, _, assum], [Context(h,[],[])] when
         let eassum = TermMan.explode_sequent assum in
         SeqHyp.get eassum.sequent_hyps 0 = Context(h,[],[]) &&
         let aconcl = eassum.sequent_concl in
         is_squash_term aconcl &&
         alpha_equal (dest_squash aconcl) concl
      ->
         [concl, SqStableGoal(Tactic_type.Tactic.tactic_of_rule tac empty_rw_args [])]
      (* H |- T --> H |- a in T *)
    | [||], [], [_, _, assum], [Context(h,[],[])] when
         is_equal_term concl &&
         let t,a,b = dest_equal concl in
         alpha_equal a b &&
         let eassum = TermMan.explode_sequent assum in
         SeqHyp.get eassum.sequent_hyps 0 = Context(h,[],[]) &&
         alpha_equal eassum.sequent_concl t
      ->
         let t,a,_ = dest_equal concl in
            [t, SqStable(a, Tactic_type.Tactic.tactic_of_rule tac empty_rw_args [])]
      (* H |- a in T *)
    | [||], [], [], [Context(_,[],[])] when
         (let t,a,b = dest_equal concl in (alpha_equal a b) )
      ->
         let t,a,_ = dest_equal concl in
            [t, SqStable(a, Tactic_type.Tactic.tactic_of_rule tac empty_rw_args [])]
      (* H; x:T; J[x] |- C[x] *)
    | [| h |], [], [], [Context(h',[],[]); Hypothesis(v,t); Context(_, [h''], [v'])] when
         h = h' && h' = h'' && is_var_term v' && (dest_var v') = v &&
         is_so_var_term concl &&
         begin match dest_so_var concl with
            _, [_; _], [v''] -> alpha_equal v' v''
          | _ -> false
         end
      ->
         let tac = funT (fun p ->
            Tactic_type.Tactic.tactic_of_rule tac { arg_ints = [| Sequent.hyp_count p |] ; arg_addrs = [||] } [])
         in
            [t, SqStable(it_term, (assertT t thenMT tac))]
    | _ ->
         raise (Invalid_argument ((string_of_loc loc) ^ ": squash_stable resource annotation:
" ^ name ^ ": the rule is not a squash-stability rule"))

(*
 * Resource.
 *)
let resource (squash_info, squash_out) squash =
   stable_resource_info unsquash_tactic

(********************************************************************
 * squash_resource info for base types                              *
 ********************************************************************)

(* For efficiency, we provide several entries for the most common types *)

let resource squash += [
   equal_term, SqUnsquash unsquashHypEqual;
   equal_term, SqStable (<<it>>, dT 0);
   equal_term, SqUnsquashGoal unsquashEqual;
   squash_term, SqStable (<<it>>, dT 0);
   squash_term, SqUnsquashGoal(unsquash);
   type_term, SqStable(<<it>>, dT 0)
]

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

doc <:doc<
   @tactics

   The @tactic[squashT] tactic uses @hrefresource[squash_resource]
   to perform the following inference:
   $$
   @rulebox{squashT; ;
      <<sequent{ <H> >- squash{'T}}>>;
      <<sequent{ <H> >- 'T}>>}
   $$
   Term $T$ must be @emph{squash-stable} and known to @hrefresource[squash_resource]
   in order for @tt[squashT] to work.

   The @tactic[unsquashT]{} tactic uses @hrefresource[squash_resource]
   to perform the following inference:
   $$
   @rulebox{unsquashT;i;
      <<sequent{ <H>; x: 'A; <J[it]> >- 'C[it]}>>;
      <<sequent{ <H>; x: squash{'A}; <J['x]> >- 'C['x]}>>}
   $$
   Either $A$ or $C[x]$ must be @emph{squash-stable} and known
   to @hrefresource[squash_resource] in order for @tt[unsquashT] to work.

   The @tt[unsquashT] tactic is added to @hrefresource[auto_resource],
   so @hreftactic[autoT] will unsquash the hypotheses whenever possible.
   @docoff
   @comment{Squash a goal}
>>
let unsquashT = argfunT (fun i p ->
   fst (Sequent.get_resource_arg p get_squash_resource) (Sequent.get_pos_hyp_num p i))

let resource nth_hyp +=
   <<squash{'a = 'b in 'T}>>, <<'a = 'b in 'T>>,
   wrap_nth_hyp_certain (fun i -> unsquashHypEqual i thenT hypothesis i)

let resource intro +=
   <<squash{'A}>>, wrap_intro (funT (fun p -> fst (get_resource_arg p get_squash_resource) 0))

let squashT = funT (fun p ->
   let ct = concl p in
      if is_squash_term ct then raise(RefineError("squashT",StringError("already squashed")))
      else squashAssert ct thenLT [ idT; unsquashT (-1) thenT trivialT ])

(* We want to see unsquashT's error message when squashElim is useless *)
let squash_elimT i =
   (progressT (squashElim i) thenT tryT (unsquashT i)) orelseT (unsquashT i)

let resource elim += (squash_term, (rule_labels_empty, true, squash_elimT))

(************************************************************************
 * AUTO TACTIC                                                          *
 ************************************************************************)

let rec collect_sqhyps hyps i =
   if i = 0 then
      []
   else
      let i' = i - 1 in
      match SeqHyp.get hyps i' with
         Hypothesis(_, t) when is_squash_term t ->
            i :: (collect_sqhyps hyps i')
      | _ ->
            collect_sqhyps hyps i'

let err = RefineError("Itt_squash.unsquashAllT", StringError "not applicable")
let unsquashAllT = funT (fun p ->
   let s = explode_sequent_arg p in
   let concl = s.sequent_concl in
   let sqconcl = is_squash_term concl in
      if sqconcl || (snd (get_resource_arg p get_squash_resource) concl) then
         match collect_sqhyps s.sequent_hyps (SeqHyp.length s.sequent_hyps) with
            [] -> raise err
          | l -> 
               if sqconcl then
                  onHypsT l unsquash 
               else
                  (squashT thenT onHypsT l unsquash thenT squashMemberFormation)
      else
         raise err)

let resource auto += {
   auto_name = "Itt_squash.unsquashAllT";
   auto_prec = trivial_prec;
   auto_tac = unsquashAllT;
   auto_type = AutoNormal;
}

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
