(*
 * Helpful rules about induction combinator.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
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

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Dependent function types.
 *)
rule set_ind_dfun_type (bind{u. 'B['u]}) :
   sequent { <H> >- isset{'s} } -->
   sequent { <H>; u: set >- "type"{'B['u]} } -->
   sequent { <H> >- fun_prop{u. 'B['u]} } -->
   sequent { <H> >- "type"{set_ind{'s; T, f, g. x: 'T -> 'B['f 'x]}} }

rule set_ind_dfun_fun (bind{x. bind{y. 'B['x; 'y]}}) :
   sequent { <H> >- fun_set{z. 'A['z]} } -->
   sequent { <H>; u: set; v: set >- "type"{'B['u; 'v]} } -->
   sequent { <H>; u: set >- fun_prop{z. 'B['u; 'z]} } -->
   sequent { <H>; v: set >- fun_prop{z. 'B['z; 'v]} } -->
   sequent { <H> >- fun_prop{z. set_ind{'A['z]; T, f, g. x: 'T -> 'B['z; 'f 'x]}} }

(*
 * Dependent product types.
 *)
rule set_ind_dprod_type (bind{u. 'B['u]}) :
   sequent { <H> >- isset{'s} } -->
   sequent { <H>; u: set >- "type"{'B['u]} } -->
   sequent { <H> >- fun_prop{u. 'B['u]} } -->
   sequent { <H> >- "type"{set_ind{'s; T, f, g. x: 'T * 'B['f 'x]}} }

rule set_ind_dprod_fun (bind{x. bind{y. 'B['x; 'y]}}) :
   sequent { <H> >- fun_set{z. 'A['z]} } -->
   sequent { <H>; u: set; v: set >- "type"{'B['u; 'v]} } -->
   sequent { <H>; u: set >- fun_prop{z. 'B['u; 'z]} } -->
   sequent { <H>; v: set >- fun_prop{z. 'B['z; 'v]} } -->
   sequent { <H> >- fun_prop{z. set_ind{'A['z]; T, f, g. x: 'T * 'B['z; 'f 'x]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
