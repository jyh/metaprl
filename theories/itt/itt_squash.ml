(*!
 * @begin[spelling]
 * squashT unhiding unsquashed unsquashEqual unsquashGoalEqual SelectOption
 * autoT squashElim squashFormation squashFromAny squashStable unsquashEqualWeak
 * SqStable SqUnsquash SqUnsquashGoal tac
 * @end[spelling]
 *
 * @begin[doc]
 * @theory[Itt_squash]
 *
 * The @tt{Itt_squash} module defines a @emph{squash} type.
 * $<<squash{'A}>>$ hides computational content of $A$.
 * $<<squash{'A}>>$ is inhabited @emph{iff} $A$ is inhabited.
 * When inhabited, $<<squash{'A}>>$ contains only one element $@it$.
 * That is $<<squash{'A}>>$ means that $A$ is true, but we do not know its
 * computational content.
 * Consequentially,  the sequent
 * $$@sequent{@it; {H; x@colon @squash{A}; J}; C}$$
 * is true when $C$ is true (with the assumption that $A$ is true),
 * but extract of $C$ does not depend on the witness of $A$.
 * Note that $x$ in this sequent stands not for a witness for $A$,
 * but just for $@it$.
 *
 * Squash types are needed to define set in @hreftheory[itt_set]. Also,
 * it can be argued (see @cite[KN01]) that it is consistent to use
 * @emph{classical} reasoning under @tt{squash} without losing
 * constructive content.
 *
 * In addition to the @tt{squash} operator on types, the @MetaPRL includes
 * the meta-theory @tt{squash} operator that works on sequents.
 * Namely, sequents in the @MetaPRL implementation of the
 * @Nuprl type theory have two forms: one is the generic
 * form $@sequent{ext; H; T}$, where @i{ext} is a variable.  The variable
 * specifies that the subproof extract may be needed for the computational content
 * of the proof.
 *
 * The other form is $@sequent{squash; H; T}$, where @hrefterm[squash] is a
 * term defined in the @hreftheory[Base_trivial]{} module.
 * The @tt{squash} term specifies that the extract of the proof of this
 * subgoal is @em{not} needed for the computational content of the whole proof.
 *
 * Typically, @tt{squash} sequents are used for well-formedness
 * goals (the computational content of well-formedness is never
 * used), but @tt{squash} sequents are also used in cases where
 * the computational content can be inferred.  Equality proofs
 * $a = b @in T$ are the canonical example: the computational content
 * of $a = b @in T$ is @emph{always} the term $@it$, and proofs
 * of equalities can always be squashed because the content can
 * be discovered later.
 *
 * The @tt{Itt_squash} module also defines a resource that can be used to
 * help prove ``squash'' stability---that is, to infer the proof
 * of a proposition given an assumption that it is true.
 *
 * This module defines a generic resource @hrefresource[squash_resource] that
 * can be used to recover computational content from a @tt{squash} proof.
 * Additions to the resource are done through resource annotations, see the
 * @hrefresource[squash_resource] section for more information. Tactics
 * @hreftactic[squashT], @hreftactic[unsquashT] and @hreftactic[sqsquashT]
 * make use of the @hrefresource[squash_resource].
 *
 * We also create a new version of @hreftactic[nthAssumT] tactic that knows how
 * to do thinning and squashing/unsquashing. This new @tt[nthAssumT] is added
 * to @hreftactic[trivialT].
 *
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
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
 * Authors:
 *   Jason Hickey @email{jyh@cs.caltech.edu}
 *   Alexei Kopylov @email{kopylov@cs.caltech.edu}
 *   Aleksey Nogin @email{nogin@cs.caltech.edu}
 *
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Itt_equal
include Itt_struct
(*! @docoff *)

open Printf
open Mp_debug
open Refiner.Refiner
open TermType
open Term
open TermOp
open TermSubst
open TermMan
open TermMeta
open RefineError
open Term_stable
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Var

open Base_dtactic
open Base_auto_tactic

open Itt_struct
open Itt_equal

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_squash%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The @tt{squash} term defines the @tt{squash} type.
 * @end[doc]
 *)
declare squash{'A}
(*! @docoff *)

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

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Equality and typehood}
 *
 * $<<squash{'A}>>$ is a type if $A$ is a type.
 * @end[doc]
 *)
prim squashEquality {| intro []; eqcd |} 'H  :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   sequent ['ext] { 'H >- squash{'A1} = squash{'A2} in univ[i:l] } = it

prim squashType {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{.squash{'A}} } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Introduction}
 *
 * A squashed type $<<squash{'A}>>$ is true if $A$ is true.
 * This rule is irreversible, so we use @tt{AutoMustComplete} to prevent @tt{autoT}
 * from using it.
 * @end[doc]
 *)
prim squashMemberFormation {| intro [AutoMustComplete] |} 'H :
   sequent [squash] { 'H >- 'A } -->
   sequent ['ext]   { 'H >- squash{'A} } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Elimination}
 *
 * The first rule, @tt{unsquashEqual}, allows equalities to
 * be unsquashed (because the proof can always be inferred).
 * The second rule, @tt{squashElim} show that $@it$ is the only element
 * of a non-empty squashed type.
 * The third rule, @tt{squashFromAny} allowed to infer a squashed
 * sequent form from any sequent form, effectively allowing us to
 * "forget" a meta-witness (extract) if we do not need it.
 * @end[doc]
 *)
prim unsquashEqualWeak 'H 'J :
   sequent [squash] { 'H; u: 'P; 'J >- 'x = 'y in 'A } -->
   sequent ['ext] { 'H; u: squash{'P}; 'J >- 'x = 'y in 'A } =
   it

prim squashElim 'H 'J :
   ('t : sequent ['ext] { 'H; u: squash{'P}; 'J[it] >- 'C[it] }) -->
   sequent ['ext] { 'H; u: squash{'P}; 'J['u] >- 'C['u] } =
   't

prim squashFromAny 'H 'ext :
   sequent ['ext] { 'H >- 'T } -->
   sequent [squash] { 'H >- 'T } =
   it

(*! @docoff *)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (squash_term,  Typeinf.infer_map dest_squash)

(************************************************************************
 * THEOREMS                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @thysection{Derived Rules}
 *
 * First, we can prove a stronger version of @tt{unsquashEqualWeak} by
 * combining it with @tt{squashElim}.
 * @end[doc]
 *)
interactive unsquashEqual 'H 'J :
   sequent [squash] { 'H; u: 'P; 'J[it] >- 'x[it] = 'y[it] in 'A[it] } -->
   sequent ['ext] { 'H; u: squash{'P}; 'J['u] >- 'x['u] = 'y['u] in 'A['u] }

(*! docoff *)
interactive unsquashWWitness 'H 'J 't:
   sequent [squash] { 'H; u: 'P; 'J[it] >- 't IN 'A[it] } -->
   sequent ['ext] { 'H; u: squash{'P}; 'J['u] >- 'A['u] }

(*!
 * @begin[doc]
 * Next, we prove that equality witness can always be recovered on meta-level.
 * @end[doc]
 *)
interactive sqsqEqual 'H :
   sequent [squash] { 'H >- 't IN 'A} -->
   sequent ['ext] { 'H >- 't IN 'A}

(*!
 * @begin[doc]
 * Next, we show that a witness of a provable hidden type is $@it$.
 * @end[doc]
 *)
interactive squashMemberEquality {| intro []; eqcd |} 'H :
   [wf] sequent [squash] { 'H >- squash{'A} } -->
   sequent ['ext] { 'H >- it IN squash{'A} }

(*!
 * @begin[doc]
 * The @tt{squashStable} rule establishes that we can unsquash a proposition
 * when it is possible to recover it's witness from simply knowing the proposition
 * to be true.
 * @end[doc]
 *)
interactive squashStable 'H 't :
   [main] sequent [squash] { 'H >- squash{'A} } -->
   [wf] sequent [squash] { 'H; x: 'A >- 't IN 'A } -->
   sequent ['ext] { 'H >- 'A}

interactive unsquashHypEqual 'H 'J :
   sequent ['ext] { 'H; u: 'x = 'y in 'A; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; u: squash{('x = 'y in 'A)}; 'J['u] >- 'C['u] }

interactive unsquash 'H 'J :
   sequent [squash] { 'H; u: 'P; 'J[it] >- squash{'T[it]} } -->
   sequent ['ext] { 'H; u: squash{'P}; 'J['u] >- squash{'T['u]} }

(*! @docoff *)
interactive unsquashStableGoal 'H 'J 'x :
   sequent [squash] { 'H; u: 'A; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; u: squash{'A}; 'J['u]; x: squash{'C['u]} >- 'C['u] } -->
   sequent ['ext] { 'H; u: squash{'A}; 'J['u] >- 'C['u]}

let unsquashStableGoalT i p =
   let h, j = Sequent.hyp_indices p i in
   let x = maybe_new_vars1 p "x" in
   unsquashStableGoal h j x p

interactive unsquashHypGoalStable 'H 'J :
   sequent ['ext] { 'H; u: 'A; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; u: squash{'A}; 'J['u] >- 'A } -->
   sequent ['ext] { 'H; u: squash{'A}; 'J['u] >- 'C['u]}

interactive unsquashStable 'H 'J 't 'x :
   sequent ['ext] { 'H; u: 'A; 'J[it] >- 'C[it] } -->
   sequent [squash] { 'H; u: squash{'A}; 'J['u]; x: 'A >- 't IN 'A } -->
   sequent ['ext] { 'H; u: squash{'A}; 'J['u] >- 'C['u]}

let unsquashStableT i t p =
   let h, j = Sequent.hyp_indices p i in
   let x = maybe_new_vars1 p "x"in
   unsquashStable h j t x p

interactive squashAssert 'H 'A :
   sequent [squash] { 'H >- squash{'A} } -->
   sequent ['ext] { 'H; x: squash{'A} >- 'C } -->
   sequent ['ext] { 'H >- 'C }

(*
 * H >- Ui ext squash(A)
 * by squashFormation
 * H >- Ui ext A
 *)
interactive squashFormation 'H :
   sequent ['ext] { 'H >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] }

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @resources
 *
 * The squash resource keeps 3 kind of tactics, as described by the
 * @tt{squash_info} type. The $@tt{SqUnsquash}(T,@i{tac})$ is used when @i{tac i}
 * is capable turning @i{i}-th hypothesis from $@squash{T}$ into $T$.
 * The $@tt{SqStable}(T,t,@i{tac})$ variant is used when @i{tac} is capable
 * of proving $@sequent{;H;t @in T}$ from $@sequent{;H;T}$. Finally,
 * the $@tt{SqUnsquashGoal}(T,@i{tac})$ is used when @i{tac i} can unsquash
 * @i{i}-th hypothesis provided the conclusion of the sequent is $T$.
 *
 * The only way to improve the @tt{squash_resource} outside of the
 * @tt{Itt_squash} theory is to use @it{resource annotations}. Currently, the
 * following kinds of rules are recognized by the @tt{squash_resource} annotations:
 * $@sequent{squash;H;A}@space@leftrightarrow@space@sequent{ext;H;t @in A}$,
 * $@sequent{ext;H;t @in A}$ and $@sequent{ext;{H; x@colon A; J[x]};C[x]}$
 * (e.g $A$ is a falsity), although it is possible
 * to add support for other kinds of rules if necessary.
 *
 * The squash resource represents data using a shape table.
 * @end[doc]
 *)
type squash_inf =
   SqUnsquash of (int -> tactic)
 | SqStable of term * tactic
 | SqUnsquashGoal of (int -> tactic)


type squash_info = term * squash_inf

(************************************************************************
 * Sequent Squash PRIMITIVES                                            *
 ************************************************************************)

let sqsquash_term = << squash >>
let sqsquash_opname = opname_of_term sqsquash_term

(*
 * Is a goal squashed?
 *)
let is_squash_sequent goal =
   let args = args_of_sequent goal in
      match dest_xlist args with
         [flag] ->
            Opname.eq (opname_of_term flag) sqsquash_opname
       | _ ->
            false

let get_squash_arg goal =
   let args = args_of_sequent goal in
      match dest_xlist args with
         [flag] ->
            flag
       | _ ->
            raise (RefineError ("get_squash_arg", StringError "no argument"))

let is_squash_goal p =
   is_squash_sequent (goal p)

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Extract an SQUASH tactic from the data.
 *)
let unsquash_tactic tbl i p =
   let conc = concl p in
   let hyp = dest_squash (snd (nth_hyp p i)) in
   match slookup_all tbl conc, slookup_all tbl hyp with
      (SqUnsquashGoal tac :: _), _ ->
         tac i p
    | _, (SqUnsquash tac :: _) ->
         tac i p
    | (SqStable (t,tac) :: _), _ ->
         let h, j = Sequent.hyp_indices p i in
            (unsquashWWitness h j t thenT tac) p
    | _, (SqStable (t,tac) :: _) ->
         (unsquashStableT i t thenLT [ idT; tac thenT trivialT]) p
    | _, (SqUnsquashGoal tac :: _) ->
         let h, j = Sequent.hyp_indices p i in
            (unsquashHypGoalStable h j thenLT [idT; tac i thenT trivialT]) p
    | (SqUnsquash tac :: _), _ ->
         (unsquashStableGoalT i thenLT [idT; tac (-1) thenT trivialT ]) p
    | [], [] ->
         raise (RefineError ("squash", StringTermError ("squash tactic doesn't know about ", mk_xlist_term [hyp;<<slot[" |- "]>>;conc])))

let process_squash_resource_annotation name contexts vars args _ stmt tac =
   let assums, goal = unzip_mfunction stmt in
   if is_squash_sequent goal then
      raise (Invalid_argument "squash_stable resource annotation: conclusion sequent should not be squashed");
   let egoal = TermMan.explode_sequent goal in
   let concl = SeqGoal.get egoal.sequent_goals 0 in
   match contexts, vars, args, assums, (SeqHyp.to_list egoal.sequent_hyps) with
      (* H |- T --> H |- a in T *)
      [|h|], [||], [], [_, _, assum], [Context(h',[])] when
         is_equal_term concl && h' = h &&
         let t,a,b = dest_equal concl in
         alpha_equal a b &&
         let eassum = TermMan.explode_sequent assum in
         SeqHyp.get eassum.sequent_hyps 0 = Context(h,[]) &&
         alpha_equal (SeqGoal.get eassum.sequent_goals 0) t
      ->
         if not (is_squash_sequent assum) then
            raise (Invalid_argument "squash_stable resource annotation: assumption sequent should be squashed");
         let t,a,_ = dest_equal concl in
         let tac p =
            let addr = Sequent.hyp_count_addr p in
            Tactic_type.Tactic.tactic_of_rule tac ([|addr|], [||]) [] p
         in
            t, SqStable(a, tac)
      (* H |- a in T *)
    | [|h|], [||], [], [], [Context(h',[])] when
         is_equal_term concl && h = h' &&
         (let t,a,b = dest_equal concl in (alpha_equal a b) )
      ->
         let t,a,_ = dest_equal concl in
         let tac p =
            let addr = Sequent.hyp_count_addr p in
            Tactic_type.Tactic.tactic_of_rule tac ([|addr|], [||]) [] p
         in
            t, SqStable(a, tac)
      (* H; x:T; J[x] |- C[x] *)
    | [| h; j |], [||], [], [], [Context(h',[]); Hypothesis(v,t); Context(j', [v'])] when
         h = h' && j = j' && is_var_term v' && (dest_var v') = v &&
         is_so_var_term concl &&
         begin match dest_so_var concl with
            _, [v''] -> alpha_equal v' v''
          | _ -> false
         end
      ->
         let tac p =
            let h, j = Sequent.hyp_indices p (-1) in
            Tactic_type.Tactic.tactic_of_rule tac ([| h; j|], [||]) [] p
         in
            t, SqStable(it_term, (assertT t thenMT tac))
    | _ ->
         raise (Invalid_argument "squash_stable resource annotation")

(*
 * Resource.
 *)
let resource squash =
   stable_resource_info unsquash_tactic

(********************************************************************
 * squash_resource info for base types                              *
 ********************************************************************)

(* For efficiency, we provide several entries for the most common types *)

let unsquashHypEqualT i p =
   let h, j = Sequent.hyp_indices p i in
   unsquashHypEqual h j p

let unsquashEqualT i p =
   let h, j = Sequent.hyp_indices p i in
   unsquashEqual h j p

let unsquashSquashT i p =
   let h, j = Sequent.hyp_indices p i in
   unsquash h j p

let resource squash += [
   equal_term, SqUnsquash unsquashHypEqualT;
   equal_term, SqStable (<<it>>, dT 0);
   equal_term, SqUnsquashGoal unsquashEqualT;
   squash_term, SqStable (<<it>>, dT 0);
   squash_term, SqUnsquashGoal(unsquashSquashT);
   type_term, SqStable(<<it>>, dT 0)
]

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*!
 * @begin[doc]
 * @tactics
 *
 * The @tactic[squashT] tactic uses @hrefresource[squash_resource]
 * to perform the following inference:
 * $$
 * @rulebox{squashT; ;
 *    @sequent{squash; H; @squash{T}};
 *    @sequent{ext; H; T}}
 * $$
 * Term $T$ must be @emph{squash-stable} and known to @hrefresource[squash_resource]
 * in order for @tt[squashT] to work.
 *
 * The @tactic[unsquashT]{} tactic uses @hrefresource[squash_resource]
 * to perform the following inference:
 * $$
 * @rulebox{unsquashT;i;
 *    @sequent{squash; {H; x@colon A; J[@it]}; C[@it]};
 *    @sequent{ext; {H; x@colon @squash{A}; J[x]}; C[x]}}
 * $$
 * Either $A$ or $C[x]$ must be @emph{squash-stable} and known
 * to @hrefresource[squash_resource] in order for @tt[unsquashT] to work.
 *
 * The @tactic[sqsquashT] tactic uses @hrefresource[squash_resource]
 * to perform the following inference:
 * $$
 * @rulebox{sqsquashT; ;
 *    @sequent{squash; H; T};
 *    @sequent{ext; H; T}}
 * $$
 * Term $T$ must be @emph{squash-stable} and known to @hrefresource[squash_resource]
 * in order for @tt[sqsquashT] to work.
 *
 * Both @tt[unsquashT] and @tt[sqsquashT] are added to @hrefresource[auto_resouce],
 * so all necessary squashing-unsquashing will be performed by @hreftactic[autoT]
 * whenever possible.
 * @docoff
 * @comment{Squash a goal}
 * @end[doc]
 *)
let unsquashT i p =
   Sequent.get_resource_arg p get_squash_resource i p

let squashT p =
   (squashAssert (hyp_count_addr p) (concl p) thenLT
      [ idT; unsquashT (-1) thenT trivialT ]) p

let resource elim += (squash_term, unsquashT)

let rec unsquashAllT_aux i seq hyps p =
   if i > hyps then idT p else
   match SeqHyp.get seq (pred i) with
      Hypothesis (_, hyp) when is_squash_term hyp ->
         (tryT (unsquashT i) thenT unsquashAllT_aux (succ i) seq hyps) p
    | _ ->
         unsquashAllT_aux (succ i) seq hyps p

let unsquashAllT p =
   unsquashAllT_aux 1 (explode_sequent p).sequent_hyps (hyp_count p) p

let sqsquashT p =
   if is_squash_goal p then
      raise (RefineError("sqsquashT", StringError("goal sequent already squashed")))
   else
      let h = hyp_count_addr p in
      (squashT thenT squashMemberFormation h) p

let unsqsquashT t p =
   squashFromAny (hyp_count_addr p) t p

(************************************************************************
 * AUTO TACTIC                                                          *
 ************************************************************************)

let nthAssumArg assum p =
   match is_squash_goal p, is_squash_sequent assum with
      false, true ->
         sqsquashT p
    | true, false ->
         unsqsquashT (get_squash_arg assum) p
    | _ ->
         idT p

let nthAssumT i p =
   let assum = Sequent.nth_assum p i in
      (Top_tacticals.thinMatchT thinT assum thenT nthAssumArg assum thenT nthAssumT i) p

let allSquashT =
   unsquashAllT thenT tryT sqsquashT

let resource auto += [{
   auto_name = "Itt_squash.nthAssumT";
   auto_prec = d_prec;
   auto_tac = onSomeAssumT nthAssumT;
   auto_type = AutoTrivial;
}; {
   auto_name = "Itt_squash.allSquashT";
   auto_prec = trivial_prec;
   auto_tac = allSquashT;
   auto_type = AutoNormal;
}]

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
