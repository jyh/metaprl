doc <:doc<
   @module[Mfir_token]

   The @tt[Mfir_token] module defines tokens, a syntactic mechanism
   for representing strings and operations on strings.
   @docoff

   ------------------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.  Additional
   information about the system is available at
   http://www.metaprl.org/

   Copyright (C) 2002 Brian Emre Aydemir, Caltech

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

   Author: Brian Emre Aydemir
   @email{emre@cs.caltech.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>

extends Mfir_bool

doc docoff

open Base_meta
open Top_conversionals

(**************************************************************************
 * Declarations.
 **************************************************************************)

doc <:doc<
   @terms

   The term @tt[token] represents a string with value @tt[str].
>>

declare token[str:s]

doc <:doc<

   Equality is the only relation defined on tokens.
>>

declare token_eq{ 'tok1; 'tok2 }

(**************************************************************************
 * Rewrites.
 **************************************************************************)

doc <:doc<
   @rewrites

   Token equality is reduced to a boolean value using a meta operation from
   the @tt[Base_meta] module.
>>

prim_rw reduce_token_eq_main :
   token_eq{ token[str1:s]; token[str2:s] } <-->
   meta_eq[str1:s, str2:s]{ "true"; "false" }

doc docoff

let reduce_token_eq =
   reduce_token_eq_main thenC reduce_meta_eq_str

let resource reduce +=
   << token_eq{ token[str1:s]; token[str2:s] } >>, reduce_token_eq

(**************************************************************************
 * Display forms.
 **************************************************************************)

dform token_df : except_mode[src] ::
   token[str:s] =
   bf["str"] `"(" slot[str:s] `")"

dform token_eq_df : except_mode[src] ::
   token_eq{ 'tok1; 'tok2 } =
   slot{'tok1} `"=" sub{it["tok"]} slot{'tok2}
