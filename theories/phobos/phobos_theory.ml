(*!
 * @spelling{MCC Mojave}
 *
 * @begin[doc]
 * @theory{Phobos Theory}
 * @module[Phobos_theory]
 *
 * The Phobos theory supplies rewrites needed for Phobos in the 
 * Mojave compiler (MCC).
 *
 * (Documentation incomplete.)
 *
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * Author: Adam Granicz
 * @email{granicz@cs.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
extends Base_meta

extends Itt_atom
extends Itt_int_base
extends Itt_int_ext
extends Itt_list
extends Itt_list2
extends Itt_rfun

extends Phobos_base

(*
 * Reduce meta_num to a number.
 *)
prim_rw reduce_meta_num : Base_meta!meta_num[n:n] <--> Itt_int_base!number[n:n]

(*
 * Add Base_meta rewrites to reduceC.
 *)
let resource reduce +=
   [<<param_add_string[p:s]{'term}>>, Phobos_base.reduce_param_add_string;
    <<error[msg:s]>>,       Phobos_base.reduce_error0;
    <<meta_num[a:n]>>,      reduce_meta_num;
    <<meta_sum[a:n,b:n]>>,  Base_meta.reduce_meta_sum;
    <<meta_diff[a:n,b:n]>>, Base_meta.reduce_meta_diff;
    <<meta_prod[a:n,b:n]>>, Base_meta.reduce_meta_prod;
    <<meta_quot[a:n,b:n]>>, Base_meta.reduce_meta_quot;
    <<meta_rem[a:n,b:n]>>,  Base_meta.reduce_meta_rem;

    <<meta_eq[a:n,b:n]{'tt; 'ff}>>, Base_meta.reduce_meta_eq_num;
    <<meta_eq[a:s,b:s]{'tt; 'ff}>>, Base_meta.reduce_meta_eq_str;
    <<meta_eq[a:v,b:v]{'tt; 'ff}>>, Base_meta.reduce_meta_eq_var;
    <<meta_eq[a:t,b:t]{'tt; 'ff}>>, Base_meta.reduce_meta_eq_tok;
    <<meta_eq[a:l,b:l]{'tt; 'ff}>>, Base_meta.reduce_meta_eq_lev;
    <<meta_lt[a:n,b:n]{'tt; 'ff}>>, Base_meta.reduce_meta_lt_num;
    <<meta_lt[a:s,b:s]{'tt; 'ff}>>, Base_meta.reduce_meta_lt_str;
    <<meta_lt[a:t,b:t]{'tt; 'ff}>>, Base_meta.reduce_meta_lt_tok;
    <<meta_lt[a:l,b:l]{'tt; 'ff}>>, Base_meta.reduce_meta_lt_lev;

    <<eq[a:n,b:n]{'tt; 'ff}>>, Phobos_base.reduce_eq_num;
    <<eq[a:s,b:s]{'tt; 'ff}>>, Phobos_base.reduce_eq_str;
    <<eq[a:v,b:v]{'tt; 'ff}>>, Phobos_base.reduce_eq_var;
    <<eq[a:t,b:t]{'tt; 'ff}>>, Phobos_base.reduce_eq_tok;
    <<eq[a:l,b:l]{'tt; 'ff}>>, Phobos_base.reduce_eq_lev;

    <<lt[a:n,b:n]{'tt; 'ff}>>, Phobos_base.reduce_lt_num;
    <<lt[a:s,b:s]{'tt; 'ff}>>, Phobos_base.reduce_lt_str;
    <<lt[a:t,b:t]{'tt; 'ff}>>, Phobos_base.reduce_lt_tok;
    <<lt[a:l,b:l]{'tt; 'ff}>>, Phobos_base.reduce_lt_lev;

    <<le[a:n,b:n]{'tt; 'ff}>>, Phobos_base.reduce_le_num;
    <<le[a:s,b:s]{'tt; 'ff}>>, Phobos_base.reduce_le_str;
    <<le[a:t,b:t]{'tt; 'ff}>>, Phobos_base.reduce_le_tok;
    <<le[a:l,b:l]{'tt; 'ff}>>, Phobos_base.reduce_le_lev;

    <<gt[a:n,b:n]{'tt; 'ff}>>, Phobos_base.reduce_gt_num;
    <<gt[a:s,b:s]{'tt; 'ff}>>, Phobos_base.reduce_gt_str;
    <<gt[a:t,b:t]{'tt; 'ff}>>, Phobos_base.reduce_gt_tok;
    <<gt[a:l,b:l]{'tt; 'ff}>>, Phobos_base.reduce_gt_lev;

    <<ge[a:n,b:n]{'tt; 'ff}>>, Phobos_base.reduce_ge_num;
    <<ge[a:s,b:s]{'tt; 'ff}>>, Phobos_base.reduce_ge_str;
    <<ge[a:t,b:t]{'tt; 'ff}>>, Phobos_base.reduce_ge_tok;
    <<ge[a:l,b:l]{'tt; 'ff}>>, Phobos_base.reduce_ge_lev ]

(*! @docoff *)
