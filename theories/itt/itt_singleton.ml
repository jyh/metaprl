(*!
 * @begin[doc]
 * @module[Itt_singleton]
 *
 * The @tt[Itt_singleton] module defines a singleton type.

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
 * Author:
 *  Alexei Kopylov @email{kopylov@cs.cornell.edu}
 *
 * @end[license]
 *)


(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
extends Itt_subtype
extends Itt_struct
extends Itt_set
extends Itt_logic

(*! @docoff *)

open Printf
open Mp_debug
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource
open Simple_print

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals
open Mptop
open Var

open Base_dtactic
open Base_auto_tactic

open Itt_struct
open Itt_logic
open Itt_subtype

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_singleton%t"

(*!
 * @begin[doc]
 * @modsection{Definition}
   By definition $<<singleton{'a;'A}>>$ is a subtype of $A$ that contain only one element $a$
   (and of course all elements equal to $a$).
 * @end[doc]
 *)

define singleton: singleton{'a;'A} <--> {x:'A | 'a='x in 'A}

(*! @docoff *)

dform singleton_df: singleton{'a;'A} = `"{" slot{'a} `"}" sub{'A}
   
(*!
 * @begin[doc]
 * @modsection{Rules}
   Rules for singleton follow immediately from the definition.
 * @end[doc]
 *)


interactive singleton_wf {| intro[] |}:
   sequent[squash]  {'H >- 'a in 'A} -->
   sequent['ext] {'H >- "type"{singleton{'a;'A}} }

interactive singleton_intro {| intro[] |}:
   sequent[squash]  {'H >- 'a = 'b in 'A} -->
   sequent['ext] {'H >- 'b in singleton{'a;'A} }

interactive singleton_elim {| elim[] |} 'H:
   sequent['ext] {'H; x : 'A; u: 'a='x in 'A; 'J['x] >- 'C['x] } -->
   sequent['ext] {'H; x : singleton{'a;'A}; 'J['x] >- 'C['x] }

interactive singleton_equal {| intro[] |}:
   sequent[squash]  {'H >- 'b  in singleton{'a;'A}} -->
   sequent[squash]  {'H >- 'c  in singleton{'a;'A}} -->
   sequent['ext] {'H >- 'b = 'c in singleton{'a;'A} }

(*! @docoff *) 
