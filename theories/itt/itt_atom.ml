doc <:doc<
   @begin[doc]
   @module[Itt_atom]

   The @tt{Itt_atom} module defines the $@atom$ type---a type of strings
   without any order relation.  The elements of the atom type are the
   @emph{tokens}.  The only comparison of tokens is equality; there is
   no elimination rule.

   The $@atom$ type is defined as primitive.  This is not strictly necessary;
   the type can be derived from the recursive type (Section @refmodule[Itt_srec]).
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

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>
extends Itt_equal
extends Itt_squiggle
doc <:doc< @docoff >>

open Lm_debug
open Lm_printf

open Basic_tactics
open Itt_equal

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_atom%t"

(* debug_string DebugLoad "Loading itt_atom..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @terms

   The @tt{atom} term defines the $@atom$ type.
   The @tt{token} term has a ``token'' parameter (a string)
   that defines the token.  The display representation of a
   token $@token{@misspelled{tok}}$ is the quoted form
   @misspelled{``tok''}.
   @end[doc]
>>
declare atom
declare token[t:t]
doc <:doc< @docoff >>

let atom_term = << atom >>
let token_term = << token[x:t] >>
let token_opname = opname_of_term token_term
let is_token_term = TermOp.is_token_term token_opname
let dest_token = TermOp.dest_token_term token_opname
let mk_token_term = TermOp.mk_token_term token_opname

let bogus_token = << token[token:t] >>

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

declare df_token[t:t] : Dform
dform atom_df : except_mode[src] :: atom = `"Atom"
dform atom_df2 : mode[src] :: atom = `"atom"
dform token_df : except_mode[src] :: token[t:t] =
   ensuremath{math_mbox{df_token[t:t]}}
dform token_df2 : df_token[t:t] =
   `"`" slot[t:t] `"'"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @rules

   @modsubsection{Equality and typehood}
   The $@atom$ term is a member of every universe, and it is a type.
   @end[doc]
>>
prim atomEquality {| intro [] |} :
   sequent { <H> >- atom in univ[i:l] } =
   it

(*
 * Typehood.
 *)
interactive atomType {| intro [] |} :
   sequent { <H> >- "type"{atom} }

doc <:doc<
   @begin[doc]
   @modsubsection{Membership}

   Two tokens are equal in the token type only if they are exactly the
   same token.
   @end[doc]
>>
prim tokenEquality {| intro [] |} :
   sequent { <H> >- token[t:t] in atom } =
   it

doc <:doc<
   @begin[doc]
   @modsubsection{Introduction}

   The $@atom$ type is always provable; the token ``t'' is
   a witness.
   @end[doc]
>>
interactive tokenFormation {| intro [] |} :
   sequent { <H> >- atom }

doc <:doc<
   @begin[doc]
   @noindent
   Two tokens in $@atom$ are computationally equivalent if they
   are equal.
   @end[doc]
>>
prim atomSqequal {| nth_hyp |} :
   sequent { <H> >- 'x = 'y in atom } -->
   sequent { <H> >- 'x ~ 'y } =
   it
doc <:doc< @docoff >>

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
 * Sqequal.
 *)
let atomSqequalT = atomSqequal

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (atom_term, infer_univ1)
let resource typeinf += (token_term, Typeinf.infer_const atom_term)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
