doc <:doc<
   @module[Itt_hoas_sequent_elim]

   The @tt[Itt_hoas_sequent_elim] module defines the tactic for
   proving the proof induction term.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2006 MetaPRL Group, California Institute of Technology

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

   Author: Aleksey Nogin @email{nogin@cs.caltech.edu}

   @end[license]
   @parents
>>
extends Itt_hoas_sequent
extends Itt_hoas_proof_ind

doc docoff

open Basic_tactics
open Itt_hoas_proof_ind

(*
 * For now, the tactic does nothing.
 *)
let elimRuleT =
   provableSequent_elim 2 twa

let elimRuleStartT =
   idT

let elimSimpleStepT =
   idT

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
