(*!
 * @begin[spelling]
 * squashT unhiding unsquashed unsquashEqual unsquashGoalEqual
 * @end[spelling]
 *
 * @begin[doc]
 * @theory[Itt_squash]
 *
 * The @tt{Itt_squash} module defines a @emph{squash} type.
 * <<squash{'A}>> hides computational content of $A$.
 * <<squash{'A}>> is inhabited iff and only if $A$ is inhabited.
 * In this case <<squash{'A}>> contains only one element $@it$.
 * That is <<squash{'A}>> means that $A$ is true, but we do not know its
 * computational content.
 * Consequentially,  the sequent
 * $$@sequent{@it; {H; x@colon {} squash{A}; J}; C}$$
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
 *    @sequent{squash; H; squash{T}};
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
 * of $a = b @in T$ is @emph{always} the term @it, and proofs
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

dform squash_df : except_mode[src] :: squash{'A} = "[" 'A "]"

dform sqsquash_df : except_mode[src] :: squash = cdot
dform sqsquash_df2 : mode[src] :: squash = `"squash"
dform it_df1 : it = cdot

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext squash(A)
 * by setFormation a A
 * H >- Ui ext A
 *)
prim squashFormation 'H 'A :
   ('A : sequent ['ext] { 'H >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] } =
   squash{'A}

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Equality and typehood}
 *
 * <<squash{'A}>> is a type if $A$ is a type.
 * @end[doc]
 *)
prim squashEquality {| intro_resource []; eqcd_resource |} 'H  :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   sequent ['ext] { 'H >- squash{'A2} = squash{'A1} in univ[i:l] } = it

prim squashType {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{.squash{'A}} } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Introduction}
 *
 * A squashed type <<squash{'A}>> is true if $A$ is true.
 * @end[doc]
 *)
prim squashMemberFormation {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- 'A } -->
   sequent ['ext]   { 'H >- squash{'A} } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Membership}
 *
 * The first rule states that witness of a provable squash type is $@it$ and
 * the second rule states the same on meta-level about sequents.
 * @end[doc]
 *)
prim squashMemberEquality {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'A } -->
   sequent ['ext] { 'H >- it IN squash{'A} } =
   it

prim squashFromAny 'H 'ext :
   sequent ['ext] { 'H >- 'T } -->
   sequent [squash] { 'H >- 'T } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Elimination}
 *
 * The next two rules allow special cases for squashed hypotheses to be
 * unsquashed.  The first rule, @tt{unsquashEqual}, allows equalities to
 * be unsquashed (because the proof can always be inferred), and the
 * @tt{unsquashGoalEqual} rule allows hypotheses to be unsquashed if
 * an equality is being proved (for the same reason).
 * @end[doc]
 *)
prim unsquashEqual 'H 'J 'u :
   ('t['u] : sequent ['ext] { 'H; u: 'x = 'y in 'A; 'J[it] >- 'C[it] }) -->
   sequent ['ext] { 'H; u: squash{('x = 'y in 'A)}; 'J['u] >- 'C['u] } =
   't[it]

prim unsquashGoalEqual 'H 'J 'u :
   sequent [squash] { 'H; u: 'P; 'J[it] >- 'x[it] = 'y[it] in 'T[it] } -->
   sequent ['ext] { 'H; u: squash{'P}; 'J['u] >- 'x['u] = 'y['u] in 'T['u] } =
   it

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let typeinf_resource =
   Mp_resource.improve typeinf_resource (squash_term,  Typeinf.infer_map dest_squash)

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
   let u, t = Sequent.nth_hyp p i in
   let t = dest_squash t in
   let j, k = Sequent.hyp_indices p i in
      if is_equal_term t then
         unsquashEqual j k u p
      else (* if is_equal_term (Sequent.concl p) then *)
         unsquashGoalEqual j k u p

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
