(*
 * Basic architecture parameters.
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

(*
 * We need more general operands during code construction.
 *)
declare ImmediateNumber{'i}
declare MemRegOff{'r; 'off}
declare MemRegRegOffMul{'r1; 'r2; 'off; 'mul}

(*
 * Size of a word on this platform, in bytes.
 *)
declare word_size

(*
 * This is the format of the header word of a given size.
 *)
declare header[i:n]
declare header{'i}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
