(*!
 * @begin[doc]
 * @theory[Itt_atom]
 *
 * The @tt{Itt_atom} module defines the $@atom$ type---a type of strings
 * without any order relation.  The elements of the atom type are the
 * @emph{tokens}.  The only comparison of tokens is equality; there is
 * no elimination rule.
 *
 * The $@atom$ type is defined as primitive.  This is not strictly necessary;
 * the type can be derived from the recursive type (Section @reftheory[Itt_srec]).
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
include Itt_equal
include Itt_squiggle
(*! @docoff *)

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Rformat
open Mp_resource

open Tactic_type

open Base_dtactic

open Itt_equal
open Itt_squiggle

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_atom%t"

(* debug_string DebugLoad "Loading itt_atom..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The @tt{atom} term defines the $@atom$ type.
 * The @tt{token} term has a ``token'' parameter (a string)
 * that defines the token.  The display representation of a
 * token $@token{@misspelled{tok}}$ is the quoted form
 * @misspelled{``tok''}.
 * @end[doc]
 *)
declare atom
declare token[t:t]
(*! @docoff *)

let atom_term = << atom >>
let token_term = << token[x:t] >>
let token_opname = opname_of_term token_term
let is_token_term = TermOp.is_token_term token_opname
let dest_token = TermOp.dest_token_term token_opname
let mk_token_term = TermOp.mk_token_term token_opname

let bogus_token = << token["token":t] >>

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform atom_df : except_mode[src] :: atom = `"Atom"
dform atom_df2 : mode[src] :: atom = `"atom"
dform token_df : except_mode[src] :: token[t:t] =
   `"`" slot[t:t] `"'"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Atom
 * by atomFormation
 *)
prim atomFormation 'H :
   sequent ['ext] { 'H >- univ[i:l] } =
   atom

(*!
 * @begin[doc]
 * @rules
 *
 * @thysubsection{Equality and typehood}
 * The $@atom$ term is a member of every universe, and it is a type.
 * @end[doc]
 *)
prim atomEquality {| intro_resource []; eqcd_resource |} 'H :
   sequent ['ext] { 'H >- atom = atom in univ[i:l] } =
   it

(*
 * Typehood.
 *)
prim atomType {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- "type"{atom} } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Introduction}
 *
 * The $@atom$ type is always provable; the token ``t'' is
 * a witness.
 * @end[doc]
 *)
prim tokenFormation 'H token[t:t] :
   sequent ['ext] { 'H >- atom } =
   token[t:t]

(*!
 * @begin[doc]
 * @thysubsection{Membership}
 *
 * Two tokens are equal in the token type only if they are exactly the
 * same token.
 * @end[doc]
 *)
prim tokenEquality {| intro_resource []; eqcd_resource |} 'H :
   sequent ['ext] { 'H >- token[t:t] = token[t:t] in atom } =
   it

(*!
 * @begin[doc]
 * @noindent
 * Two tokens in $@atom$ are computationally equivalent if they
 * are equal.
 * @end[doc]
 *)
prim atomSqequal 'H :
   sequent [squash] { 'H >- 'x = 'y in atom } -->
   sequent ['ext] { 'H >- 'x ~ 'y } =
   it
(*! @docoff *)

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let atom_term = << atom >>
let token_term = << token[x:t] >>
let token_opname = opname_of_term token_term
let is_token_term = TermOp.is_token_term token_opname
let dest_token = TermOp.dest_token_term token_opname
let mk_token_term = TermOp.mk_token_term token_opname

(*
 * D
 *)
let bogus_token = << token["token":t] >>

(*
 * Sqequal.
 *)
let atomSqequalT p =
   atomSqequal (Sequent.hyp_count_addr p) p

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let typeinf_resource = Mp_resource.improve typeinf_resource (atom_term, infer_univ1)
let typeinf_resource =
   Mp_resource.improve typeinf_resource (token_term, Typeinf.infer_const atom_term)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
