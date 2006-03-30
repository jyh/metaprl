(*
 * Additional well-formedness rule for bterms.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2005-2006 Mojave Group, Caltech
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
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
extends Itt_hoas_normalize

open Basic_tactics

(*
 * Push the bind into the term.
 *)
topval bindWFT : tactic
topval proofRuleAuxWFT : tactic
topval proofRuleWFT : tactic

(*
 * Debugging.
 *)
topval proofRule1T : tactic
topval proofRule2T : tactic
topval proofRule3T : tactic
topval proveArithT : tactic

(*
 * This will eventually go back into the standard library.
 *)
resource (term * unit, tactic) forward_subst

topval forward_substT : tactic

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
