(*!
 * @begin[doc]
 * @theory[Itt_equal]
 *
 * The @tt{Itt_equal} module defines type @emph{universes},
 * @emph{cumulativity} of type universes, and equality.
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
 * Author: Jason Hickey
 * @email{jyh@cs.caltech.edu}
 *
 * @end[license]
 *)

(*!************************************************************************
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Base_theory
(*! @docoff *)
include Itt_comment

open Printf
open Mp_debug
open String_set
open Opname
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermType
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermMeta
open Refiner.Refiner.RefineError
open Rformat
open Simple_print
open Term_stable
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Mptop

open Base_meta
open Base_dtactic
open Base_auto_tactic

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_equal%t"

let debug_eqcd =
   create_debug (**)
      { debug_name = "eqcd";
        debug_description = "display eqcd operations";
        debug_value = false
      }

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*!************************************************************************
 * @begin[doc]
 * @terms
 *
 * The universe type $@univ{i}$ is a @emph{type of types}.  The individual type
 * universe judgments are listed in the modules for each of the types.
 * Furthermore, there is no elimination rule, since each universe is just a set of
 * points, with no order.
 *
 * The $@cumulativity{i; j}$ term is a primitive judgment that defines level
 * @emph{inclusion} (this is a builtin judgment in @MetaPRL).
 *
 * The $@type{t}$ term is used to define the @emph{type} judgment.  A term $T$ is a
 * type if $@sequent{squash; H; @type{T}}$.
 *
 * The semantic meaning of an open equality is that:
 * @begin[enumerate]
 * @item{$T$ is a type,}
 * @item{$t_1$ and $t_2$ are well-formed elements of type $T$.}
 * @item{and $t_1$ and $t_2$ are equal using the equality of type $T$.}
 * @end[enumerate]
 * @end[doc]
 *)
declare "type"{'a}
declare univ[i:l]
declare equal{'T; 'a; 'b}
declare cumulativity[i:l, j:l]
(*! @docoff *)

declare "true"
declare "false"

let true_term = << "true" >>
let true_opname = opname_of_term true_term
let is_true_term = is_no_subterms_term true_opname

let false_term = << "false" >>
let false_opname = opname_of_term false_term
let is_false_term = is_no_subterms_term false_opname

let cumulativity_term = << cumulativity[i:l, j:l] >>

let equal_term = << 'a = 'b in 'c >>
let equal_opname = opname_of_term equal_term
let is_equal_term = is_dep0_dep0_dep0_term equal_opname
let dest_equal = dest_dep0_dep0_dep0_term equal_opname
let mk_equal_term = mk_dep0_dep0_dep0_term equal_opname

let is_member_term t =
   is_equal_term t &&
   match dest_equal t with
      _, t1, t2 -> alpha_equal t1 t2

let type_term = << "type"{'t} >>
let type_opname = opname_of_term type_term
let is_type_term = is_dep0_term type_opname
let mk_type_term = mk_dep0_term type_opname
let dest_type_term = dest_dep0_term type_opname

let univ_term = << univ[i:l] >>
let univ1_term = << univ[1:l] >>
let univ_opname = opname_of_term univ_term
let is_univ_term = TermOp.is_univ_term univ_opname
let dest_univ = TermOp.dest_univ_term univ_opname
let mk_univ_term = TermOp.mk_univ_term univ_opname

let unknown_level = dest_univ << univ[unknown:l] >>

let try_dest_univ t =
   if is_univ_term t then dest_univ t else unknown_level

let it_term = << it >>

(************************************************************************
 * EQCD RESOURCE                                                        *
 ************************************************************************)

(*
 * Extract an EQCD tactic from the data.
 * The tactic checks for an optable.
 *)
let extract_data tbl =
   let eqcd p =
      let t = Sequent.concl p in
      let _, l, _ = dest_equal t in
         try
            (* Find and apply the right tactic *)
            if !debug_eqcd then
               eprintf "Itt_equal.eqcd: looking up %s%t" (SimplePrint.string_of_opname (opname_of_term l)) eflush;
            let tac = slookup tbl l in
               if !debug_eqcd then
                  eprintf "Itt_equal.eqcd: found a tactic for %s%t" (SimplePrint.string_of_opname (opname_of_term l)) eflush;
               tac p
         with
            Not_found ->
               raise (RefineError ("eqcd", StringTermError ("EQCD tactic doesn't know about ", l)))
   in
      eqcd

(*
 * Add info from a rule definition.
 *)
let process_eqcd_resource_annotation name context_args var_args term_args _ statement pre_tactic =
   let _, goal = unzip_mfunction statement in
   let t =
      try TermMan.nth_concl goal 1 with
         RefineError _ ->
            raise (Invalid_argument (sprintf "Itt_equal.improve_intro: %s: must be an introduction rule" name))
   in
   let _, t, _ =
      try dest_equal t with
         RefineError _ ->
            raise (Invalid_argument (sprintf "Itt_equal.improve_intro: %s must be an equality judgement" name))
   in
   let term_args =
      match term_args with
         [] ->
            (fun _ -> [])
       | _ ->
            let length = List.length term_args in
               (fun p ->
                     let args =
                        try get_with_args p with
                           RefineError _ ->
                              raise (RefineError (name, StringIntError ("arguments required", length)))
                     in
                     let length' = List.length args in
                        if length' != length then
                           raise (RefineError (name, StringIntError ("wrong number of arguments", length')));
                        args)
   in
   let tac =
      match context_args with
         [|_|] ->
            (fun p ->
                  let vars = Var.maybe_new_vars_array p var_args in
                  let addr = Sequent.hyp_count_addr p in
                     Tactic_type.Tactic.tactic_of_rule pre_tactic ([| addr |], vars) (term_args p) p)
       | _ ->
            raise (Invalid_argument (sprintf "Itt_equal.intro: %s: not an introduction rule" name))
   in
      (t, tac)

(*
 * Resource.
 *)
let resource eqcd =
   stable_resource_info extract_data

(*
 * Resource argument.
 *)
let eqcdT p =
   Sequent.get_resource_arg p get_eqcd_resource p

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

prim_rw reduce_cumulativity' : cumulativity[i:l, j:l] <-->
   meta_lt{univ[i:l]; univ[j:l]; ."true"; ."false"}

let reduce_cumulativity =
   reduce_cumulativity' thenC reduce_meta_lt

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_type
prec prec_equal

dform equal_df : except_mode[src] :: parens :: "prec"[prec_equal] :: equal{'T; 'a; 'b} =
   szone pushm slot{'a} space `"= " slot{'b} space Nuprl_font!member `" " slot{'T} popm ezone

dform equal_df2 : mode[src] :: parens :: "prec"[prec_equal] :: equal{'T; 'a; 'b} =
   szone pushm slot{'a} space `"= " slot{'b} space `"in " slot{'T} popm ezone

(* HACK! - this should be replaced with a proper I/O abstraction *)
dform member_df : except_mode[src] :: parens :: "prec"[prec_equal] :: ('x IN 'T) =
   szone pushm slot{'x} space Nuprl_font!member hspace slot{'T} popm ezone

dform member_df2 : mode[src] :: parens :: "prec"[prec_equal] :: ('x IN 'T) =
   szone pushm slot{'x} space `"IN" hspace slot{'T} popm ezone

dform type_df1 : except_mode[src] :: parens :: "prec"[prec_type] :: "type"{'a} =
   math_type{'a}

dform type_df2 : mode[src] :: "type"{'a} =
   `"\"type\"{" slot{'a} `"}"

dform univ_df1 : except_mode[src] :: univ[i:l] =
   math_univ{slot[i:l]}

dform cumulativity_df : cumulativity[i:l, j:l] =
   `"cumulativity[" slot[i:l] `";" slot[j:l] `"]"

dform squash_df : except_mode[src] :: squash = cdot
dform squash_df2 : mode[src] :: squash = `"squash"
dform it_df1 : it = cdot

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * True always holds.
 *)
prim trueIntro {| intro [] |} 'H :
   sequent ['ext] { 'H >- "true" } =
   it

(*!************************************************************************
 * @begin[doc]
 * @rules
 *
 * @thysubsection{Equality axiom}
 *
 * The @emph{axiom} rule declares that if a program $x$ has type
 * $T$ by assumption, then $T$ is a type, and $x$ is a member of $T$.
 * @end[doc]
 *)
prim equalityAxiom 'H 'J :
   sequent ['ext] { 'H; x: 'T; 'J['x] >- 'x IN 'T } =
   it

(*!************************************************************************
 * @begin[doc]
 * @thysubsection{Equality is an equivalence relation}
 *
 * The next three rules specify that equality is an equivalence relation.
 * The @emph{reflexivity} rule differs from the standard definition:
 * a program $x$ has type $T$ if it is equal to any other
 * element of $T$.
 * @end[doc]
 *)

(*
 * Reflexivity.
 *)
prim equalityRef 'H 'y :
   sequent ['ext] { 'H >- 'x = 'y in 'T } -->
   sequent ['ext] { 'H >- 'x IN 'T } =
   it

(*
 * Symmetry.
 *)
prim equalitySym 'H :
   sequent ['ext] { 'H >- 'y = 'x in 'T } -->
   sequent ['ext] { 'H >- 'x = 'y in 'T } =
   it

(*
 * Transitivity.
 *)
prim equalityTrans 'H 'z :
   sequent ['ext] { 'H >- 'x = 'z in 'T } -->
   sequent ['ext] { 'H >- 'z = 'y in 'T } -->
   sequent ['ext] { 'H >- 'x = 'y in 'T } =
   it

(*
 * H >- Ui ext a = b in T
 * by equalityFormation T
 *
 * H >- T ext a
 * H >- T ext b
 *)
prim equalityFormation 'H 'T :
   [main] ('a : sequent ['ext] { 'H >- 'T }) -->
   [main] ('b : sequent ['ext] { 'H >- 'T }) -->
   sequent ['ext] { 'H >- univ[i:l] } =
   'a = 'b in 'T

(*!************************************************************************
 * @begin[doc]
 * @thysubsection{Well-formedness of equality}
 *
 * The next two rules describe well-formedness of the equality judgment.
 * Equality is @emph{intensional}: two equalities are equal if all of their
 * parts are equal.
 * @end[doc]
 *)

(*
 * H >- (a1 = b1 in T1) = (a2 = b2 in T2)
 * by equalityEquality
 *
 * H >- T1 = T2 in Ui
 * H >- a1 = a2 in T1
 * H >- b1 = b2 in T1
 *)
prim equalityEquality {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'T1 = 'T2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'a1 = 'a2 in 'T1 } -->
   [wf] sequent [squash] { 'H >- 'b1 = 'b2 in 'T2 } -->
   sequent ['ext] { 'H >- ('a1 = 'b1 in 'T1) = ('a2 = 'b2 in 'T2) in univ[i:l] } =
   it

(*
 * Typehood.
 *)
prim equalityType {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a IN 'T } -->
   [wf] sequent [squash] { 'H >- 'b IN 'T } -->
   sequent ['ext] { 'H >- "type"{. 'a = 'b in 'T } } =
   it

(*! @docoff *)
interactive equalityType2 {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a IN 'T } -->
   sequent ['ext] { 'H >- "type"{. 'a IN 'T } }

(*!************************************************************************
 * @begin[doc]
 * @thysubsection{Inhabitants of the equality types}
 *
 * The two following rules state that $@it$ is the one-and-only element
 * in a provable equality or a provable @tt{Type} type.
 * @end[doc]
 *)

(*
 * H >- it in (a = b in T)
 * by axiomMember
 *
 * H >- a = b in T
 *)
prim axiomMember {| intro []; eqcd |} 'H :
   [wf] sequent [squash] { 'H >- 'a = 'b in 'T } -->
   sequent ['ext] { 'H >- it IN ('a = 'b in 'T) } =
   it

(*
 * H, x: a = b in T, J[x] >- C[x]
 * by equalityElimination i
 *
 * H, x: a = b in T; J[it] >- C[it]
 *)
prim equalityElimination {| elim [] |} 'H 'J :
   ('t : sequent ['ext] { 'H; x: 'a = 'b in 'T; 'J[it] >- 'C[it] }) -->
   sequent ['ext] { 'H; x: 'a = 'b in 'T; 'J['x] >- 'C['x] } =
   't

prim type_axiomMember {| intro []; eqcd |} 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent ['ext] { 'H >- it IN "type"{'T} } =
   it

(*!************************************************************************
 * @begin[doc]
 * @thysubsection{Truth implies typehood}
 *
 * For any sequent judgment $@sequent{ext; H; T}$ the term $T$ must be a
 * a type.  The following rule allows us to infer well-formedness of a
 * type from it provability.  Note that this rule is useless for types $T$
 * that are not true.
 * @end[doc]
 *)

(*
 * H >- T = T in type
 * by typeEquality
 *
 * H >- T
 *)
prim typeEquality 'H :
   [main] sequent [squash] { 'H >- 'T } -->
   sequent ['ext] { 'H >- "type"{'T} } =
   it

(*!************************************************************************
 * @begin[doc]
 * @thysubsection{Universe cumulativity}
 *
 * The following two rules describe universe @emph{cumulativity}.
 * The $@cumulativity{i:l; j:l}$ term is a built-in judgment
 * describing level inclusion.
 * @end[doc]
 *)

(*
 * H >- Uj in Ui
 * by universeMember (side (j < i))
 *
 * Add a tactic later that will automatically
 * unfold the cumulativity.
 *)
prim universeMember 'H :
   sequent ['ext] { 'H >- cumulativity[j:l, i:l] } -->
   sequent ['ext] { 'H >- univ[j:l] IN univ[i:l] } =
  it

(*
 * H >- x = x in Ui
 * by universeCumulativity
 *
 * H >- x = x in Uj
 * H >- cumulativity(j, i)
 *)
prim universeCumulativity 'H univ[j:l] :
   sequent [squash] { 'H >- cumulativity[j:l, i:l] } -->
   sequent [squash] { 'H >- 'x = 'y in univ[j:l] } -->
   sequent ['ext] { 'H >- 'x = 'y in univ[i:l] } =
   it

(*! @docoff *)
let univ_member_term = << univ[i:l] IN univ[j:l] >>

let eqcd_univT p =
   let i = Sequent.hyp_count_addr p in
      (universeMember i
       thenT tryT (rw reduce_cumulativity 0 thenT trueIntro i)) p

let resource eqcd += (univ_term, eqcd_univT)
let resource intro += (univ_member_term, wrap_intro eqcd_univT)

(*!************************************************************************
 * @begin[doc]
 * @thysubsection{The type universe is a type}
 *
 * The next three rules state that every universe $@univ{l}$ is a type, and
 * every inhabitant $x @in @univ{l}$ is also a type.
 * @end[doc]
 *)
prim universeType {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{univ[l:l]} } =
   it

(*
 * Anything in a universe is a type.
 *)
prim universeMemberType 'H univ[i:l] :
   [wf] sequent [squash] { 'H >- 'x IN univ[i:l] } -->
   sequent ['ext] { 'H >- "type"{'x} } =
   it

(*
 * Derived form for known membership.
 * hypothesis rule is not know yet.
 *)
prim universeAssumType 'H 'J :
   sequent ['ext] { 'H; x: univ[l:l]; 'J['x] >- "type"{'x} } =
   it

(*! @docoff *)
let univTypeT t p =
   universeMemberType (Sequent.hyp_count_addr p) t p

(*
 * H >- Ui ext Uj
 * by universeFormation
 *)
prim universeFormation 'H univ[j:l] :
   sequent ['ext] { 'H >- cumulativity[j:l, i:l] } -->
   sequent ['ext] {'H >- univ[i:l] } =
   univ[j:l]

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Infer types from membership and equality.
 *)
let infer_equal subst (so, t) =
   let t, x1, x2 = dest_equal t in
   let subst =
      if is_var_term x1 then
         (dest_var x1, t) :: subst
      else
         subst
   in
      if is_var_term x2 then
         (dest_var x2, t) :: subst
      else
         subst

let resource typeinf_subst += (equal_term, infer_equal)

(*
 * Type of a universe is incremented by one.
 *)
let inf_univ _ _ _ eqs opt_eqs defs t =
   let le = dest_univ t in
      eqs, opt_eqs, defs, mk_univ_term (incr_level_exp le)

let resource typeinf += (univ_term, inf_univ)

(*
 * Type of an equality is the type of the equality type.
 *)
let equal_type t =
   let ty, _, _ = dest_equal t in ty

let resource typeinf += (equal_term, Typeinf.infer_map equal_type)

(*
 * Helper functions for universe type inference
 *)

let infer_univ_dep0_dep0 destruct inf consts decls eqs opt_eqs defs t =
   let a, b = destruct t in
   let eqs', opt_eqs', defs', a' = inf consts decls eqs opt_eqs defs a in
   let eqs'', opt_eqs'', defs'', b' = inf consts decls eqs' opt_eqs' defs' b in
   let eqs''', opt_eqs''', subst, a'' = Typeinf.typeinf_final consts eqs'' opt_eqs'' defs'' a' in
   let b'' = apply_subst (apply_subst b' subst) defs in
   let le1 = try_dest_univ a'' in
   let le2 = try_dest_univ b'' in
      eqs''', opt_eqs''', defs'', mk_univ_term (max_level_exp le1 le2 0)

let infer_univ_dep0_dep1 destruct inf consts decls eqs opt_eqs defs t =
   let v, a, b = destruct t in
   let eqs', opt_eqs', defs', a' = inf consts decls eqs opt_eqs defs a in
   let eqs'', opt_eqs'', defs'', b' =
      inf (StringSet.add v consts) ((v,a)::decls) eqs' opt_eqs' defs' b in
   let eqs''', opt_eqs''', subst, a'' = Typeinf.typeinf_final consts eqs'' opt_eqs'' defs'' a' in
   let b'' = apply_subst (apply_subst b' subst) defs in
   let le1 = try_dest_univ a'' in
   let le2 = try_dest_univ b'' in
      eqs''', opt_eqs''', defs'', mk_univ_term (max_level_exp le1 le2 0)

let infer_univ1 = Typeinf.infer_const univ1_term

(************************************************************************
 * OTHER TACTICS                                                        *
 ************************************************************************)

(*
 * H, x:T, J >- x = x in T
 *)
let equalAssumT i p =
   let i, j = Sequent.hyp_indices p i in
      equalityAxiom i j p

(*
 * Assumed membership.
 *)
let univAssumT i p =
   let j, k = Sequent.hyp_indices p i in
      universeAssumType j k p

(*
 * Automation.
 *
 * let triv_equalT i p =
 *    (equalAssumT i
 *    orelseT univAssumT i) p
 *)
let triv_equalT i p =
   let i, j = Sequent.hyp_indices p i in
   (equalityAxiom i j orelseT universeAssumType i j) p

(*
 * Reflexivity.
 *)
let equalRefT t p =
   equalityRef (Sequent.hyp_count_addr p) t p

(*
 * Symettry.
 *)
let equalSymT p =
   equalitySym (Sequent.hyp_count_addr p) p

(*
 * Transitivity.
 *)
let equalTransT t p =
   equalityTrans (Sequent.hyp_count_addr p) t p

(*
 * Universe cumulativity.
 *)
let cumulativityT u p =
   let i = Sequent.hyp_count_addr p in
      (universeCumulativity i u
       thenLT [tryT (rw reduce_cumulativity 0 thenT trueIntro i); idT]) p

(*
 * Typehood from truth.
 *)
let typeAssertT p =
   typeEquality (Sequent.hyp_count_addr p) p

let resource trivial += {
   auto_name = "triv_equalT";
   auto_prec = trivial_prec;
   auto_tac = onSomeHypT triv_equalT
}

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
