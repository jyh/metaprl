(*
 * Valid kinds.
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
 *)

include Lf_sig;;

declare equal{'A; 'B};;

(*
 * Const family.
 *)
rule const_fam 'S 'C :
   ctx{'S1[hyp{'K; c. 'S2[nil_sig; 'c]}]; 'C[nil_ctx]} -->
   sequent { 'S1; c. 'K; 'S2['c]; 'C['c] >> mem{'c; 'K}};;

(*
 * Kind equality.
 *)
rule conv_fam 'S 'C :
   sequent { 'S; 'C >> mem{'A; 'K1 } } -->
   sequent { 'S; 'C >> 'K2 } -->
   sequent { 'S; 'C >> equal{'K1; 'K2} } -->
   sequent { 'S; 'C >> mem{'A; 'K2} };;

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
