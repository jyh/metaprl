(*
 * Primitiva interactiveatization of implication.
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

extends Czf_itt_sep

open Lm_debug
open Lm_printf

open Dtactic

(*
 * We need the allAutoT tactic from Czf_itt_all,
 * but we don't need the logic.
 *)

let _ =
   show_loading "Loading Czf_itt_exists%t"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Implication is restricted.
 *)
interactive dprod_fun3 {| intro [] |} :
   ["wf"]   sequent { <H>; u: set >- "type"{'A['u]} } -->
   ["wf"]   sequent { <H>; u: set; z: 'A['u] >- "type"{'B['u; 'z]} } -->
   sequent { <H> >- fun_prop{z. 'A['z]} } -->
   sequent { <H> >- dfun_prop{z. 'A['z]; u, v. 'B['u; 'v]} } -->
   sequent { <H> >- fun_prop{z. "prod"{'A['z]; w. 'B['z; 'w]}} }

interactive dprod_res {| intro [] |} :
   sequent { <H> >- restricted{'A} } -->
   sequent { <H>; u: 'A >- restricted{'B['u]} } -->
   sequent { <H> >- restricted{."prod"{'A; u. 'B['u]}} }

interactive exists_fun {| intro [] |} :
   ["wf"]   sequent { <H>; u: set >- "type"{'A['u]} } -->
   ["wf"]   sequent { <H>; u: set; z: 'A['u] >- "type"{'B['u; 'z]} } -->
   sequent { <H> >- fun_prop{z. 'A['z]} } -->
   sequent { <H> >- dfun_prop{z. 'A['z]; u, v. 'B['u; 'v]} } -->
   sequent { <H> >- fun_prop{z. "exists"{'A['z]; w. 'B['z; 'w]}} }

interactive exists_res {| intro [] |} :
   sequent { <H> >- restricted{'A} } -->
   sequent { <H>; u: 'A >- restricted{'B['u]} } -->
   sequent { <H> >- restricted{."exists"{'A; u. 'B['u]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
