(*!
 * @spelling{squashT}
 *
 * @begin[doc]
 * @theory[Itt_squash]
 *
 * The @tt{Itt_squash} module defines a resource that can be used to
 * help prove ``squash'' stability---that is, to infer the proof
 * of a proposition given an assumption that it is true.
 *
 * Sequents in the @Nuprl type theory have two forms: one is the generic
 * form $@sequent{ext; H; T}$, where @i{ext} is a variable.  The variable
 * specifies that the proof extract is needed for the computational content
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
 * Certain rules are valid only for @tt{squash} sequents; rules for
 * using squashed assertions in the ``set'' type (in the @hreftheory[Itt_set])
 * module), for example.  Also, it can be argued that it is consistent to use
 * @emph{classical} reasoning on @tt{squash} goals without losing
 * constructive content.
 *
 * This module defines a generic resource @hrefresource[squash_resource] that
 * can be used to recover computational content from a @tt{squash} proof.
 * The resource defines a tactic @hreftactic[squashT] that performs the
 * following inference:
 *
 * $$
 * @rulebox{squashT; ;
 *    @sequent{squash; H; T};
 *    @sequent{ext; H; T}}
 * $$
 *
 * Additions to the resource require two arguments: a @emph{term} that
 * matches the conclusion of the squashed goal, and a tactic that performs
 * squash reduction on goals of that form.
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

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Base_theory
(*! @docoff *)
include Itt_comment

open Printf
open Mp_debug
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Term_stable
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_squash%t"

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform squash_df : except_mode[src] :: squash = cdot
dform squash_df2 : mode[src] :: squash = `"squash"
dform it_df1 : it = cdot

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

let squash_term = << squash >>
let squash_opname = opname_of_term squash_term

(*
 * Is a goal squashed?
 *)
let is_squash_sequent goal =
   let args = args_of_sequent goal in
      match dest_xlist args with
         [flag] ->
            Opname.eq (opname_of_term flag) squash_opname
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

(*!
 * @begin[doc]
 * @tactics
 *
 * The @tactic[squashT]{} tactic is defined as a proof annotation
 * that is passed down the proof.  The tactic retrieves the
 * annotation and applies it to the current goal.
 *
 * @docoff
 * @end[doc]
 *)
let squashT p =
   Sequent.get_tactic_arg p "squash" p

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
