(*
 * We need a rule for when rewrites are valid.
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

include Rewrite_type
include Base_dtactic

open Refiner.Refiner.RefineError
open Nl_resource

open Tacticals
open Rewrite_type

(*
 * Template for the term.
 *)
let rewrite_term = << "rewrite"{'a; 'b} >>

(*
 * The dtactic operation only works on a concl.
 *)
let d_rewriteT i p =
   if i = 0 then
      rewriteSequentAxiom (Sequent.hyp_count_addr p) p
   else
      raise (RefineError ("d_rewriteT", StringError "can't decompose a rewrite hyp"))

let d_resource = d_resource.resource_improve d_resource (rewrite_term, d_rewriteT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
