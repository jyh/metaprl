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
include Mptop
include Summary

(*
 * Meta-operations.
 *)
declare meta_sum{'a; 'b}
declare meta_diff{'a; 'b}
declare meta_prod{'a; 'b}
declare meta_quot{'a; 'b}
declare meta_rem{'a; 'b}

declare meta_eq{'a; 'b; 'tt; 'ff}
declare meta_le{'a; 'b; 'tt; 'ff}
declare meta_lt{'a; 'b; 'tt; 'ff}

(*
 * sum{op1[@i1:n]; op2[@i2:n]} --> op1[@i1 + @i2]
 *)
ml_rw reduce_meta_sum : meta_sum{'a; 'b}
ml_rw reduce_meta_diff : meta_diff{'a; 'b}
ml_rw reduce_meta_prod : meta_prod{'a; 'b}
ml_rw reduce_meta_quot : meta_quot{'a; 'b}
ml_rw reduce_meta_rem  : meta_rem{'a; 'b}
ml_rw reduce_meta_eq : meta_eq{'a; 'b; 'tt; 'ff}
ml_rw reduce_meta_lt : meta_lt{'a; 'b; 'tt; 'ff}
ml_rw reduce_meta_le : meta_le{'a; 'b; 'tt; 'ff}

(*
 * -*-
 * Local Variables:
 * Caml-master: "mp.run"
 * End:
 * -*-
 *)
