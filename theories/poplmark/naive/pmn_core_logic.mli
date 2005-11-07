(*
 * Logic for core FSub.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2005 Mojave Group, Caltech
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
extends Pmn_core_terms

(************************************************************************
 * Sequents.
 *
 * We care only about sequents that use appropriate terms from Fsub.
 *)
declare Sequent

(************************************************************************
 * Propositions.
 *)
declare fsub_prop{'e : Prop} : Nonterminal

production fsub_prop{fsub_subtype{'ty1; 'ty2}} <--
   fsub_exp{'ty1}; tok_st; fsub_exp{'ty2}

production fsub_prop{fsub_member{'e; 'ty}} <--
   fsub_exp{'e}; tok_colon; fsub_exp{'ty}

(************************************************************************
 * Sequents.
 *)
declare typeclass parsed_hyps_exp

declare iform parsed_sequent{'e : Judgment} : Term

declare fsub_hyps{'e : parsed_hyps_exp} : Nonterminal
declare fsub_nonempty_hyps{'e : parsed_hyps_exp} : Nonterminal
declare fsub_hyp[x:s]{'e : 'a} : Nonterminal

declare sequent [parsed_hyps] { exst a: Hyp. TyElem{'a} : 'a >- Ignore } : parsed_hyps_exp

production xterm_simple_term{parsed_sequent{sequent [fsub] { <H> >- 'e }}} <--
   tok_fsub; tok_left_sequent; fsub_hyps{parsed_hyps{| <H> |}}; tok_turnstile; fsub_prop{'e}; tok_right_sequent

production fsub_hyps{parsed_hyps{||}} <--
   (* empty *)

production fsub_hyps{'e} <--
   fsub_nonempty_hyps{'e}

production fsub_nonempty_hyps{parsed_hyps{| x: 'e |}} <--
   fsub_hyp[x:s]{'e}

production fsub_nonempty_hyps{parsed_hyps{| <hyps>; x : 'e |}} <--
   fsub_nonempty_hyps{parsed_hyps{| <hyps> |}}; tok_semi; fsub_hyp[x:s]{'e}

production fsub_hyp[x:s]{TyVal{'e}} <--
   tok_id[x:s]; tok_colon; fsub_exp{'e}

production fsub_hyp[x:s]{TyPower{'e}} <--
   tok_id[x:s]; tok_st; fsub_exp{'e}

production fsub_hyp[""]{'c} <--
   xterm_context{'c}

iform parsed_sequent :
   parsed_sequent{'e}
   <-->
   'e

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
