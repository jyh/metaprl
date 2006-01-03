(*
 * Forms for context induction.
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
extends Base_theory

open Basic_tactics

(*
 * The meta-lambda calculus.
 *)
declare type HFun{'a : Ty; 'b : Ty; 'c : Ty}

declare hlambda{'B : 'b; x : 'a. 'e['x] : 'c} : HFun{'a; 'b; 'c}
declare happly{'h : HFun{'a; 'b; 'c}; 'e : 'a} : 'c
declare htype{'h : HFun{'a; 'b; 'c}} : 'b

(*
 * Sequent constructors.
 *)
declare concl{'arg : ty_sequent{ty_hyp{'a; 'b}; 'c; 'd}; 'concl : 'c} : 'd
declare hyp{'B : 'b; x : 'a. 'e['x] : 'd} : 'd

(*
 * Destructors.
 *)
declare sequent_ind{x : ty_sequent{ty_hyp{'a; 'b}; 'c; 'd}, y : 'c. 'concl['x; 'y] : 'result;
                    h : HFun{'a; 'b; 'result}. 'step['h] : 'result;
                    'e : 'd} : 'result

(*
 * Core destructor.
 *)
declare type SequentCore{'a : Ty; 'b : Ty; 'c : Ty}

declare sequent [SequentTerm] { 'a : 'b >- 'c } : SequentCore{'a; 'b; 'c}

declare sequent_ind{h: HFun{'a; 'b; 'result}. 'step['h] : 'result; 'e : SequentCore{'a; 'b; 'result}} : 'result

(*
 * Terms.
 *)
val mk_hyp_term : var -> term -> term -> term
val dest_hyp_term : term -> var * term * term

val mk_hlambda_term : var -> term -> term -> term
val dest_hlambda_term : term -> var * term * term

topval reduce_concl_conv : conv

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
