doc <:doc<
   @begin[doc]
   @module[Itt_equal]

   The @tt{Itt_equal} module defines type @emph{universes},
   @emph{cumulativity} of type universes, and equality.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 1998 Jason Hickey, Cornell University

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
>>

doc <:doc< ************************************************************************
   @begin[doc]
   @parents
   @end[doc]
>>
extends Base_theory
doc <:doc< @docoff >>
extends Itt_comment

open Printf
open Lm_debug
open Lm_symbol
open Lm_string_set
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
open Dtactic
open Auto_tactic

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

doc <:doc<
   @begin[doc]
   @terms

   The universe type $@univ{i}$ is a @emph{type of types}.  The individual type
   universe judgments are listed in the modules for each of the types.
   Furthermore, there is no elimination rule, since each universe is just a set of
   points, with no order.

   The $@type{t}$ term is used to define the @emph{type} judgment.  A term $T$ is a
   type if <<sequent{ <H> >- 'T Type}>>.

   The semantic meaning of an open equality is that:
   @begin[enumerate]
   @item{$T$ is a type,}
   @item{$t_1$ and $t_2$ are well-formed elements of type $T$.}
   @item{and $t_1$ and $t_2$ are equal using the equality of type $T$.}
   @end[enumerate]
   @end[doc]
>>
declare "type"{'a}
declare equal{'T; 'a; 'b}
declare univ[i:l]
doc docoff
(*
 * XXX HACK:
 * Type theory should have its own sequent_arg, but instead it uses
 * Base_rewrite!sequent_arg - this is necessary because the conditional rewrites
 * take their semantics from both Base theory and ITT
declare sequent_arg
 *)

declare "true"
declare "false"

doc <:doc<
   @begin[doc]
   The $@cumulativity{i; j}$ term is a primitive judgment that defines level
   @emph{inclusion} (this is a builtin judgment in @MetaPRL).
   @end[doc]
>>
define unfold_cumulativity :
   cumulativity[i:l, j:l] <--> meta_lt[i:l, j:l]{."true"; ."false"}
doc docoff

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

let complete_unless_member =
   CondMustComplete (fun p -> not (is_member_term (Sequent.concl p)))

let type_term = << 't Type >>
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
               tac
         with
            Not_found ->
               raise (RefineError ("eqcd", StringTermError ("EQCD tactic doesn't know about ", l)))
   in
      funT eqcd

(*
 * Add info from a rule definition.
 *)
let process_eqcd_resource_annotation name context_args term_args _ statement pre_tactic =
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
         [||] ->
            funT (fun p ->
                Tactic_type.Tactic.tactic_of_rule pre_tactic [| |] (term_args p))
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
let eqcdT =
   funT (fun p -> Sequent.get_resource_arg p get_eqcd_resource)

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

let reduce_cumulativity =
   unfold_cumulativity thenC reduce_meta_lt_lev

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_type
prec prec_equal

dform equal_df : except_mode[src] :: parens :: "prec"[prec_equal] :: equal{'T; 'a; 'b} =
   szone pushm slot["le"]{'a} space `"= " slot["le"]{'b} space Nuprl_font!member `" " slot["le"]{'T} popm ezone

dform equal_df2 : mode[src] :: parens :: "prec"[prec_equal] :: equal{'T; 'a; 'b} =
   szone pushm slot["le"]{'a} space `"= " slot["le"]{'b} space `"in " slot["le"]{'T} popm ezone

(* HACK! - this should be replaced with a proper I/O abstraction *)
dform member_df : except_mode[src] :: parens :: "prec"[prec_equal] :: ('x in 'T) =
   szone pushm slot["le"]{'x} space Nuprl_font!member hspace slot["le"]{'T} popm ezone

dform member_df2 : mode[src] :: parens :: "prec"[prec_equal] :: ('x in 'T) =
   szone pushm slot["le"]{'x} space `"in" hspace slot["le"]{'T} popm ezone

dform type_df1 : except_mode[src] :: parens :: "prec"[prec_type] :: ('a Type) =
   math_type{'a}

dform type_df2 : mode[src] :: ('a Type) =
   slot{'a} `" Type"

dform univ_df1 : except_mode[src] :: univ[i:l] =
   math_univ{slot[i:l]}

dform cumulativity_df : cumulativity[i:l, j:l] =
   `"cumulativity[" slot[i:l] `";" slot[j:l] `"]"

dform it_df1 : except_mode[src] :: it = cdot
dform it_df2 : mode[src] :: it = `"it"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * True always holds.
 *)
prim trueIntro {| intro [] |} :
   sequent { <H> >- "true" } =
   it

doc <:doc< ************************************************************************
   @begin[doc]
   @rules

   @modsubsection{Equality axiom}

   The @emph{axiom} rule declares that if a program $x$ has type
   $T$ by assumption, then $T$ is a type, and $x$ is a member of $T$.
   @end[doc]
>>
prim equalityAxiom 'H :
   sequent { <H>; x: 'T; <J['x]> >- 'x in 'T } =
   it

doc <:doc< ************************************************************************
   @begin[doc]
   @modsubsection{Equality is an equivalence relation}

   The next three rules specify that equality is an equivalence relation.
   The @emph{reflexivity} rule differs from the standard definition:
   a program $x$ has type $T$ if it is equal to any other
   element of $T$.
   @end[doc]
>>

(*
 * Reflexivity.
 *)
prim equalityRef 'y :
   sequent { <H> >- 'x = 'y in 'T } -->
   sequent { <H> >- 'x in 'T } =
   it

(*
 * Symmetry.
 *)
prim equalitySym :
   sequent { <H> >- 'y = 'x in 'T } -->
   sequent { <H> >- 'x = 'y in 'T } =
   it

(*
 * Transitivity.
 *)
prim equalityTrans 'z :
   sequent { <H> >- 'x = 'z in 'T } -->
   sequent { <H> >- 'z = 'y in 'T } -->
   sequent { <H> >- 'x = 'y in 'T } =
   it

(*
 * H >- Ui ext a = b in T
 * by equalityFormation T
 *
 * H >- T ext a
 * H >- T ext b
 *)
prim equalityFormation 'T :
   [main] ('a : sequent { <H> >- 'T }) -->
   [main] ('b : sequent { <H> >- 'T }) -->
   sequent { <H> >- univ[i:l] } =
   'a = 'b in 'T

doc <:doc< ************************************************************************
   @begin[doc]
   @modsubsection{Well-formedness of equality}

   The next two rules describe well-formedness of the equality judgment.
   Equality is @emph{intensional}: two equalities are equal if all of their
   parts are equal.
   @end[doc]
>>

(*
 * H >- (a1 = b1 in T1) = (a2 = b2 in T2)
 * by equalityEquality
 *
 * H >- T1 = T2 in Ui
 * H >- a1 = a2 in T1
 * H >- b1 = b2 in T1
 *)
prim equalityEquality {| intro [] |} :
   [wf] sequent { <H> >- 'T1 = 'T2 in univ[i:l] } -->
   [wf] sequent { <H> >- 'a1 = 'a2 in 'T1 } -->
   [wf] sequent { <H> >- 'b1 = 'b2 in 'T2 } -->
   sequent { <H> >- ('a1 = 'b1 in 'T1) = ('a2 = 'b2 in 'T2) in univ[i:l] } =
   it

(*
 * Typehood.
 *)
prim equalityType {| intro [] |} :
   [wf] sequent { <H> >- 'a in 'T } -->
   [wf] sequent { <H> >- 'b in 'T } -->
   sequent { <H> >- ('a = 'b in 'T) Type } =
   it

doc <:doc< ************************************************************************
   @begin[doc]
   @modsubsection{Inhabitants of the equality types}

   The two following rules state that $@it$ is the one-and-only element
   in a provable equality or a provable @tt{Type} type.
   @end[doc]
>>

(*
 * H >- it in (a = b in T)
 * by axiomMember
 *
 * H >- a = b in T
 *)
prim axiomMember {| intro []; eqcd |} :
   [wf] sequent { <H> >- 'a = 'b in 'T } -->
   sequent { <H> >- it in ('a = 'b in 'T) } =
   it

(*
 * H, x: a = b in T, J[x] >- C[x]
 * by equalityElimination i
 *
 * H, x: a = b in T; J[it] >- C[it]
 *)
prim equalityElimination {| elim [] |} 'H :
   ('t['x] : sequent { <H>; x: 'a = 'b in 'T; <J[it]> >- 'C[it] }) -->
   sequent { <H>; x: 'a = 'b in 'T; <J['x]> >- 'C['x] } =
   't[it]

prim type_axiomMember {| intro []; eqcd |} :
   sequent { <H> >- 'T Type } -->
   sequent { <H> >- it in ('T Type) } =
   it

doc <:doc< ************************************************************************
   @begin[doc]
   @modsubsection{Truth implies typehood}

   For any sequent judgment <<sequent{ <H> >- 'T}>> the term $T$ must be a
   type.  The following rule allows us to infer well-formedness of a
   type from its provability.  Note that this rule is useless for types $T$
   that are not true.
   @end[doc]
>>

(*
 * H >- T = T in type
 * by typeEquality
 *
 * H >- T
 *)
prim typeEquality :
   [main] sequent { <H> >- 'T } -->
   sequent { <H> >- 'T Type } =
   it

doc <:doc< ************************************************************************
   @begin[doc]
   @modsubsection{Universe cumulativity}

   The following two rules describe universe @emph{cumulativity}.
   The $@cumulativity{i:l; j:l}$ term is a built-in judgment
   describing level inclusion.
   @end[doc]
>>

(*
 * H >- Uj in Ui
 * by universeMember (side (j < i))
 *
 * Add a tactic later that will automatically
 * unfold the cumulativity.
 *)
prim universeMember :
   sequent { <H> >- cumulativity[j:l, i:l] } -->
   sequent { <H> >- univ[j:l] in univ[i:l] } =
  it

(*
 * H >- x = x in Ui
 * by universeCumulativity
 *
 * H >- x = x in Uj
 * H >- cumulativity(j, i)
 *)
prim universeCumulativity univ[j:l] :
   sequent { <H> >- cumulativity[j:l, i:l] } -->
   sequent { <H> >- 'x = 'y in univ[j:l] } -->
   sequent { <H> >- 'x = 'y in univ[i:l] } =
   it

doc <:doc< @docoff >>
let univ_member_term = << univ[i:l] in univ[j:l] >>

let eqcd_univT =
   universeMember thenT tryT (rw reduce_cumulativity 0 thenT trueIntro)

let resource eqcd += (univ_term, eqcd_univT)
let resource intro += (univ_member_term, wrap_intro eqcd_univT)

doc <:doc< ************************************************************************
   @begin[doc]
   @modsubsection{The type universe is a type}

   The next three rules state that every universe $@univ{l}$ is a type, and
   every inhabitant $x @in @univ{l}$ is also a type.
   @end[doc]
>>
prim universeMemberType univ[i:l] :
   [wf] sequent { <H> >- 'x in univ[i:l] } -->
   sequent { <H> >- 'x Type } =
   it

(*
 * Derived form for known membership.
 * hypothesis rule is not know yet.
 *)
interactive universeAssumType 'H :
   sequent { <H>; x: univ[l:l]; <J['x]> >- 'x Type }

interactive universeType {| intro [] |} :
   sequent { <H> >- univ[l:l] Type }

doc <:doc< @docoff >>
let univTypeT = universeMemberType

(*
 * H >- Ui ext Uj
 * by universeFormation
 *)
prim universeFormation univ[j:l] :
   sequent { <H> >- cumulativity[j:l, i:l] } -->
   sequent { <H> >- univ[i:l] } =
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
      inf (SymbolSet.add consts v) ((v,a)::decls) eqs' opt_eqs' defs' b in
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
let equalAssumT = equalityAxiom

(*
 * Assumed membership.
 *)
let univAssumT = universeAssumType

(*
 * Reflexivity, Symettry, Transitivity.
 *)
let equalRefT = equalityRef
let equalSymT = equalitySym
let equalTransT = equalityTrans

(*
 * Universe cumulativity.
 *)
let cumulativityT u =
   universeCumulativity u thenLT [tryT (rw reduce_cumulativity 0 thenT trueIntro); idT]

(*
 * Typehood from truth.
 *)
let typeAssertT = typeEquality

(*
 * Automation.
 *)
let triv_equalT =
   argfunT (fun i p ->
   let concl = Sequent.concl p in
   let hyp = Sequent.nth_hyp p i in
      if is_type_term concl then
         let _ = dest_univ hyp in univAssumT i
      else
         let gt, ga, gb = dest_equal concl in
         if alpha_equal gt hyp then equalAssumT i else
         let ht, ha, hb = dest_equal hyp in
         if alpha_equal gt ht then
            if alpha_equal ga gb then
               if alpha_equal ha ga then equalRefT hb
               else if alpha_equal hb ga then equalRefT ha thenT equalSymT
               else if alpha_equal ha gb && alpha_equal hb ga then equalSymT
               else raise generic_refiner_exn
            else raise generic_refiner_exn
         else raise generic_refiner_exn)

let equality_prec = create_auto_prec [trivial_prec] []

let resource auto += {
   auto_name = "Itt_equal.triv_equalT";
   auto_prec = equality_prec;
   auto_tac = onSomeHypT triv_equalT;
   auto_type = AutoTrivial;
}

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
