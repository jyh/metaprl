(*
 * We need a rule for when rewrites are valid.
 *
 * ----------------------------------------------------------------
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
 * Author: Jason Hickey <jyh@cs.cornell.edu>
 * Modified By: Aleksey Nogin <nogin@cs.caltech.edu>
 *)

extends Perv
extends Auto_tactic

open Refiner.Refiner.TermType

open Tactic_type.Tacticals
open Tactic_type.Conversionals

declare sequent_arg

rule rewriteAxiom1 :
   sequent { <H> >- Perv!"rewrite"{'a; 'a} }

rewrite rewriteAxiom2 'a 'b : (Perv!"rewrite"{'a; 'b}) --> 'a <--> 'b

rule rewriteSym :
   sequent { <H> >- Perv!"rewrite"{'a; 'b} } -->
   sequent { <H> >- Perv!"rewrite"{'b; 'a} }

topval rewriteC : term -> conv
topval rewriteT : term -> tactic
topval rewriteSymT : tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
