(*
 * Basic parameters of the runtime.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003 Jason Hickey, Caltech
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
extends M_ir
extends M_arith
extends M_x86_asm

open Top_conversionals

(*
 * We need more general operands during code construction.
 *)
declare ImmediateNumber{'i}
declare MemRegOff{'r; 'off}
declare MemRegRegOffMul{'r1; 'r2; 'off; 'mul}

dform immediate_number_df : ImmediateNumber{number[i:n]} =
   `"$" slot[i:n]

dform immediate_number_df : ImmediateNumber{'i} =
   `"$( " slot{'i} `" )"

dform mem_reg_off_df : MemRegOff{'r; 'off} =
   slot{'off} `"<" slot{'r} `">"

dform mem_reg_reg_off_mul_df : MemRegRegOffMul{'r1; 'r2; 'off; 'mul} =
   `"<" slot{'r1} `"," slot{'r2} `"," slot{'off} `"," slot{'mul} `">"

prim_rw fold_immediate_number {| reduce |} :
   ImmediateNumber{number[i:n]} <--> ImmediateNumber[i:n]

prim_rw fold_mem_reg_off {| reduce |} :
   MemRegOff{'r; number[off:n]} <--> MemRegOff[off:n]{'r}

prim_rw fold_mem_reg_reg_off_mul {| reduce |} :
   MemRegRegOffMul{'r1; 'r2; number[off:n]; number[mul:n]} <--> MemRegRegOffMul[off:n, mul:n]{'r1; 'r2}

(*
 * Size of a word on this platform, in bytes.
 *)
define unfold_word_size {| reduce |} : word_size <--> number[4:n]

dform word_size_df : word_size = `"$word_size"

(*
 * This is the format of the header word of a given size.
 *)
declare header[i:n]
declare header{'i}

dform header_df1 : header[i:n] =
   bf["header["] slot[i:n] bf["]"]

dform header_df2 : header{'i} =
   bf["header<"] slot{'i} bf[">"]

prim_rw unfold_header {| reduce |} : header[i:n] <--> ImmediateNumber{mul{number[i:n]; word_size}}
prim_rw fold_header {| reduce |} : header{number[i:n]} <--> header[i:n]

doc docoff

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
