(*
 * Miscellaneous rewrites for Phobos.
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
 * Copyright (C) 2002 Adam Granicz, Caltech
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
 * Author: Adam Granicz <granicz@cs.caltech.edu>
 *
 *)
extends Shell
extends Summary

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError

extends Base_meta

(*
 * Terms.
 *)
declare "true"
declare "false"

declare eq[a:n, b:n]{'t; 'f}
declare eq[a:s, b:s]{'t; 'f}
declare eq[a:v, b:v]{'t; 'f}
declare eq[a:t, b:t]{'t; 'f}
declare eq[a:l, b:l]{'t; 'f}

declare lt[a:n, b:n]{'t; 'f}
declare lt[a:s, b:s]{'t; 'f}
declare lt[a:t, b:t]{'t; 'f}
declare lt[a:l, b:l]{'t; 'f}

declare le[a:n, b:n]{'t; 'f}
declare le[a:s, b:s]{'t; 'f}
declare le[a:t, b:t]{'t; 'f}
declare le[a:l, b:l]{'t; 'f}

declare gt[a:n, b:n]{'t; 'f}
declare gt[a:s, b:s]{'t; 'f}
declare gt[a:t, b:t]{'t; 'f}
declare gt[a:l, b:l]{'t; 'f}

declare ge[a:n, b:n]{'t; 'f}
declare ge[a:s, b:s]{'t; 'f}
declare ge[a:t, b:t]{'t; 'f}
declare ge[a:l, b:l]{'t; 'f}

(*
 * Phobos error terms.
 *)
declare error[msg:s]

(*
 * Parameter operations.
 *)
declare param_add_string[s:s]{'term}

(*
 * Rewrite tactics.
 *)
ml_rw reduce_error0 : error[msg:s]
ml_rw reduce_param_add_string : param_add_string[s:s]{'term}

rewrite reduce_eq_num : eq[a:n, b:n]{'t; 'f} <--> meta_eq[a:n, b:n]{'t; 'f}
rewrite reduce_eq_str : eq[a:s, b:s]{'t; 'f} <--> meta_eq[a:s, b:s]{'t; 'f}
rewrite reduce_eq_var : eq[a:v, b:v]{'t; 'f} <--> meta_eq[a:v, b:v]{'t; 'f}
rewrite reduce_eq_tok : eq[a:t, b:t]{'t; 'f} <--> meta_eq[a:t, b:t]{'t; 'f}
rewrite reduce_eq_lev : eq[a:l, b:l]{'t; 'f} <--> meta_eq[a:l, b:l]{'t; 'f}

rewrite reduce_lt_num : lt[a:n, b:n]{'t; 'f} <--> meta_lt[a:n, b:n]{'t; 'f}
rewrite reduce_lt_str : lt[a:s, b:s]{'t; 'f} <--> meta_lt[a:s, b:s]{'t; 'f}
rewrite reduce_lt_tok : lt[a:t, b:t]{'t; 'f} <--> meta_lt[a:t, b:t]{'t; 'f}
rewrite reduce_lt_lev : lt[a:l, b:l]{'t; 'f} <--> meta_lt[a:l, b:l]{'t; 'f}

rewrite reduce_le_num : le[a:n, b:n]{'t; 'f} <--> meta_lt[b:n, a:n]{'f; 't}
rewrite reduce_le_str : le[a:s, b:s]{'t; 'f} <--> meta_lt[b:s, a:s]{'f; 't}
rewrite reduce_le_tok : le[a:t, b:t]{'t; 'f} <--> meta_lt[b:t, a:t]{'f; 't}
rewrite reduce_le_lev : le[a:l, b:l]{'t; 'f} <--> meta_lt[b:l, a:l]{'f; 't}

rewrite reduce_gt_num : gt[a:n, b:n]{'t; 'f} <--> meta_lt[b:n, a:n]{'t; 'f}
rewrite reduce_gt_str : gt[a:s, b:s]{'t; 'f} <--> meta_lt[b:s, a:s]{'t; 'f}
rewrite reduce_gt_tok : gt[a:t, b:t]{'t; 'f} <--> meta_lt[b:t, a:t]{'t; 'f}
rewrite reduce_gt_lev : gt[a:l, b:l]{'t; 'f} <--> meta_lt[b:l, a:l]{'t; 'f}

rewrite reduce_ge_num : ge[a:n, b:n]{'t; 'f} <--> meta_lt[a:n, b:n]{'f; 't}
rewrite reduce_ge_str : ge[a:s, b:s]{'t; 'f} <--> meta_lt[a:s, b:s]{'f; 't}
rewrite reduce_ge_tok : ge[a:t, b:t]{'t; 'f} <--> meta_lt[a:t, b:t]{'f; 't}
rewrite reduce_ge_lev : ge[a:l, b:l]{'t; 'f} <--> meta_lt[a:l, b:l]{'f; 't}

(*
 * -*-
 * Local Variables:
 * Caml-master: "mp.run"
 * End:
 * -*-
 *)
