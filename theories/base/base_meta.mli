(*
 * Basic arithmetic operations.
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

extends Shell
extends Summary

(*
 * Meta-operations.
 *)
declare meta_num[n:n]
declare meta_sum[a:n, b:n]
declare meta_diff[a:n, b:n]
declare meta_prod[a:n, b:n]
declare meta_quot[a:n, b:n]
declare meta_rem[a:n, b:n]

declare meta_eq[a:n,b:n]{'tt; 'ff}
declare meta_eq[a:s,b:s]{'tt; 'ff}
declare meta_eq[a:t,b:t]{'tt; 'ff}
declare meta_eq[a:l,b:l]{'tt; 'ff}

declare meta_lt[a:n,b:n]{'tt; 'ff}
declare meta_lt[a:s,b:s]{'tt; 'ff}
declare meta_lt[a:t,b:t]{'tt; 'ff}
declare meta_lt[a:l,b:l]{'tt; 'ff}

(*
 * sum{op1[@i1:n]; op2[@i2:n]} --> op1[@i1 + @i2]
 *)
ml_rw reduce_meta_sum : meta_sum[a:n, b:n]
ml_rw reduce_meta_diff : meta_diff[a:n, b:n]
ml_rw reduce_meta_prod : meta_prod[a:n, b:n]
ml_rw reduce_meta_quot : meta_quot[a:n, b:n]
ml_rw reduce_meta_rem  : meta_rem[a:n, b:n]

ml_rw reduce_meta_eq_num : meta_eq[a:n,b:n]{'tt; 'ff}
ml_rw reduce_meta_eq_str : meta_eq[a:s,b:s]{'tt; 'ff}
ml_rw reduce_meta_eq_tok : meta_eq[a:t,b:t]{'tt; 'ff}
ml_rw reduce_meta_eq_lev : meta_eq[a:l,b:l]{'tt; 'ff}

ml_rw reduce_meta_lt_num : meta_lt[a:n, b:n]{'tt; 'ff}
ml_rw reduce_meta_lt_str : meta_lt[a:s, b:s]{'tt; 'ff}
ml_rw reduce_meta_lt_tok : meta_lt[a:t, b:t]{'tt; 'ff}
ml_rw reduce_meta_lt_lev : meta_lt[a:l, b:l]{'tt; 'ff}

(*
 * -*-
 * Local Variables:
 * Caml-master: "mp.run"
 * End:
 * -*-
 *)
