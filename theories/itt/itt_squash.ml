(*!
 * @begin[spelling]
 * squashT unhiding unsquashed unsquashEqual unsquashGoalEqual SelectOption
 * autoT squashElim squashFormation squashFromAny squashStable unsquashEqualWeak
 * @end[spelling]
 *
 * @begin[doc]
 * @theory[Itt_squash]
 *
 * The @tt{Itt_squash} module defines a @emph{squash} type.
 * $<<squash{'A}>>$ hides computational content of $A$.
 * $<<squash{'A}>>$ is inhabited iff and only if $A$ is inhabited.
 * In this case $<<squash{'A}>>$ contains only one element $@it$.
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
 * The @tt{Itt_squash} module also defines a resource that can be used to
 * help prove ``squash'' stability---that is, to infer the proof
 * of a proposition given an assumption that it is true.
 *
 * This module defines a generic resource @hrefresource[squash_resource] that
 * can be used to recover computational content from a @tt{squash} proof.
 * The resource defines a tactic @hreftactic[squashT] that performs the
 * following inference:
 *
 * $$
 * @rulebox{squashT; ;
 *    @sequent{squash; H; @squash{T}};
 *    @sequent{ext; H; T}}
 * $$
 *
 * Additions to the resource require two arguments: a @emph{term} that
 * matches the conclusion of the goal, and a tactic that performs
 * squash reduction on goals of that form.
 *
 * In addition to the @tt{squash} operator on types, the @MetaPRL includes
 * the meta-theory @tt{squash} operator that works on sequents.
 * Namely, sequents in the @Nuprl type theory have two forms: one is the generic
 * form $@sequent{ext; H; T}$, where @i{ext} is a variable.  The variable
 * specifies that the proof extract may be needed for the computational content
 * of the proof.
 *
 * The other form is $@sequent{squash; H; T}$, where @hrefterm[squash] is a
 * term defined in the @hreftheory[Base_trivial]{} module.
 * The @tt{squash} term specifies that the proof
 * extract is @em{not} needed for its computational content.
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
open Term
open TermOp
open TermMan
open TermSubst
open RefineError
open Term_stable
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Var

open Base_dtactic

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
prim squashEquality {| intro_resource []; eqcd_resource |} 'H  :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   sequent ['ext] { 'H >- squash{'A1} = squash{'A2} in univ[i:l] } = it

prim squashType {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{.squash{'A}} } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Introduction}
 *
 * A squashed type $<<squash{'A}>>$ is true if $A$ is true.
 * This rule is irreversible, so we use @tt{SelectOption 0} to prevent @tt{autoT}
 * from using it.
 * @end[doc]
 *)
prim squashMemberFormation {| intro_resource [SelectOption 0] |} 'H :
   [wf] sequent [squash] { 'H >- 'A } -->
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

let typeinf_resource =
   Mp_resource.improve typeinf_resource (squash_term,  Typeinf.infer_map dest_squash)

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
interactive squashMemberEquality {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- squash{'A} } -->
   sequent ['ext] { 'H >- it IN squash{'A} }

(*!
 * @begin[doc]
 * The @tt{squashStable} rule establishes that we can unsquash a proposition
 * when it is possible to recover it's witness from simply knowing the proposition
 * to be true.
 * @end[doc]
 *)

interactive squashStable 'H 'J 't :
   [main] sequent [squash] { 'H >- squash{'A} } -->
   [wf] sequent [squash] { 'H; x: 'A >- 't IN 'A } -->
   sequent ['ext] { 'H >- 'A}

interactive unsquashHypEqual 'H 'J :
   sequent ['ext] { 'H; u: 'x = 'y in 'A; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; u: squash{('x = 'y in 'A)}; 'J['u] >- 'C['u] }

interactive unsquash 'H 'J :
   sequent [squash] { 'H; u: 'P; 'J[it] >- squash{'T[it]} } -->
   sequent ['ext] { 'H; u: squash{'P}; 'J['u] >- squash{'T['u]} }

(*!
 * @docoff
 *
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

(*
 * Keep a table of tactics to prove squash stability.
 *)
type squash_data = tactic term_stable

(*!
 * @begin[doc]
 * @resources
 *
 * The squash resource represents data using a table that maps
 * goal terms to the tactic that performs squash inference on
 * goals of that form.  The argument @code{term * tactic} specifies
 * the matching term and the tactic.
 * @end[doc]
 *)
resource (term * tactic, tactic, squash_data, unit) squash_resource
(*! @docoff *)

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Extract an SQUASH tactic from the data.
 * The tactic checks for an optable.
 *)
let extract_data base =
   let tbl = sextract base in
   let squash p =
      let t = concl p in
         try (slookup tbl t) p with
            Not_found ->
               raise (RefineError ("squash", StringTermError ("SQUASH tactic doesn't know about ", t)))
   in
      squash

(*
 * Wrap up the joiner.
 *)
let join_resource = join_stables

let extract_resource = extract_data

let improve_resource data (t, tac) =
   sinsert data t tac

let close_resource rsrc modname =
   rsrc

(*
 * Resource.
 *)
let squash_resource =
   Mp_resource.create (**)
      { resource_join = join_resource;
        resource_extract = extract_resource;
        resource_improve = improve_resource;
        resource_improve_arg = Mp_resource.improve_arg_fail "squash_resource";
        resource_close = close_resource
      }
      (new_stable ())

let get_resource modname =
   Mp_resource.find squash_resource modname

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let sqsquash_term = << squash >>
let sqsquash_opname = opname_of_term squash_term

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
 * TACTICS                                                              *
 ************************************************************************)

(*!
 * @begin[doc]
 * @tactics
 *
 * The @tactic[squashT]{} tactic is defined as a proof annotation
 * that is passed down the proof.  The tactic retrieves the
 * annotation and applies it to the current goal.
 *
 * @docoff
 * @comment{Squash a goal}
 * @end[doc]
 *)
let squashT p =
   Sequent.get_tactic_arg p "squash" p

let unsquashT i p =
   let t = Sequent.concl p in
   let j, k = Sequent.hyp_indices p i in
      if is_equal_term t then
         unsquashEqual j k p
      else if is_squash_term t then
         unsquash j k p
      else (* if is_equal_term (dest_squash (fst (Sequent.nth_hyp p i)) then *)
         unsquashHypEqual j k p

let elim_resource =
   Mp_resource.improve elim_resource (squash_term, unsquashT)

let sqsquashT =
   squashT thenT dT 0

let unsqsquashT t p =
   squashFromAny (Sequent.hyp_count_addr p) t p

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
