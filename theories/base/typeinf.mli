(*
 * Before anything, we start the type inference resource.
 * This is mostly an incomplete type inference algorithm, but
 * it is used to perform basic inference.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
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
 * jyh@cs.cornell.edu
 *)

include Tacticals

open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst

open Sequent
open Tacticals

(*
 * A type inference is performed in a type context,
 * which maps variables to type.
 *
 * The inference infers the type for a term in the given context,
 * or it throws the exception (TypeInfer t) for a term "t" that
 * doesn't have an inferable type.
 *)

(*
 * This is the type of the inference algorithm.
 *)
type typeinf_func = unify_subst -> term -> unify_subst * term

(*
 * Modular components also get a recursive instance of
 * the inference algorithm.
 *)
type typeinf_comp = typeinf_func -> typeinf_func

(*
 * This is the resource addition.
 *)
type typeinf_resource_info = term * typeinf_comp

(*
 * Internal type.
 *)
type typeinf_data

(*
 * The resource itself.
 *)
resource (typeinf_resource_info, typeinf_func, typeinf_data) typeinf_resource

(*
 * Resources that have been created.
 *)
val get_resource : string -> typeinf_resource

(*
 * Utilities.
 *)
val typeinf_of_proof : tactic_arg -> typeinf_func
val infer_type : tactic_arg -> term -> unify_subst * term

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
