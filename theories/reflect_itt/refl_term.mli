(*
 * Terms modulo alpha-equality.
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
 *
 *)

include Refl_raw_term

open Refiner.Refiner.TermType

open Tactic_type.Tacticals
open Tactic_type.Conversionals

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare eq_alpha{'t1; 't2}
declare eq_alpha_term{'f; 't1; 't2}
declare eq_alpha_bterm{'f; 'bt1; 'bt2}

declare vmap_type
declare vmap_nil
declare vmap_cons{'v1; 'v2; 'vmap}
declare vmap_compose{'vl1; 'vl2; 'vm; g. 'b['g]}
declare vmap_compare{'v1; 'v2; 'vm}
declare vmap_invert{'f}
declare vmap_id{'f}
declare vmap_length{'f; 'g}
declare vmap_join{'f; 'g}
declare vmap_fst{'f}
declare vmap_snd{'f}

declare bterm_type{'T}
declare term_type

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_vmap_compose
prec prec_vmap_fst

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * Variable maps.
 *)
topval unfold_vmap_type : conv
topval unfold_vmap_nil : conv
topval unfold_vmap_cons : conv
topval unfold_vmap_compose : conv
topval unfold_vmap_compare : conv
topval unfold_vmap_invert : conv
topval unfold_vmap_id : conv
topval unfold_vmap_length : conv
topval unfold_vmap_join : conv
topval unfold_vmap_fst : conv
topval unfold_vmap_snd : conv
topval unfold_eq_alpha : conv
topval unfold_eq_alpha_term : conv
topval unfold_eq_alpha_bterm : conv
topval unfold_term_type : conv

topval fold_vmap_type : conv
topval fold_vmap_nil : conv
topval fold_vmap_cons : conv
topval fold_vmap_compose : conv
topval fold_vmap_compare : conv
topval fold_vmap_invert : conv
topval fold_vmap_id : conv
topval fold_vmap_length : conv
topval fold_vmap_join : conv
topval fold_vmap_fst : conv
topval fold_vmap_snd : conv
topval fold_eq_alpha : conv
topval fold_eq_alpha_term : conv
topval fold_eq_alpha_bterm : conv
topval fold_term_type : conv

(*
 * Tactics.
 *)
topval vmapSymT : tactic
topval vmapTransT : term -> term -> tactic

topval eq_alphaRefT : tactic
topval eq_alphaSymT : tactic
topval eq_alphaTransT : term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "mp.run"
 * End:
 * -*-
 *)
