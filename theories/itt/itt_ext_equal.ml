(*
 * This module defines some extra features _after_ equality
 * and subtyping have been defined.  This includes the "type"
 * judgement, and extensional type equality.
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
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)

open Lm_debug

extends Itt_equal
extends Itt_squash
extends Itt_subtype
extends Itt_logic

open Itt_squash
open Dtactic
open Tactic_type.Tacticals
open Tactic_type.Conversionals

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_ext_equal%t"

(*
 * Terms type{'T} and \subtype{'A; 'B} have already been defined.
 *)
prim_rw type_def : "type"{'T} <--> ('T subtype 'T)

define unfoldExtEqual : ext_equal{'A; 'B} <--> 'A subtype 'B & 'B subtype 'A

dform extEqual_df : ext_equal{'A; 'B} =  'A `" =" sube `" " 'B 

interactive extEqualMember {|squash; intro[] |}: 
   sequent{ <H> >- ext_equal{'A;'B}} -->
   sequent{ <H> >- (it,it) in ext_equal{'A;'B} }

let resource intro +=
   [<<ext_equal{'A; 'B}>>, wrap_intro (rw unfoldExtEqual 0 thenT dT 0);
    <<"type"{ext_equal{'A; 'B}}>>, wrap_intro (rw unfoldExtEqual 0 thenT dT 0 thenT dT 0)
   ]

let resource elim += (<<ext_equal{'A; 'B}>>, (fun n -> rw unfoldExtEqual n thenT dT n))
                        
(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
