(*
 * Valid signatures.
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

declare sig{'S};;
declare nil_sig;;
declare mem{'A; 'B};;
declare type;;

(*
 * Valid signatures.
 *)
rule nil_sig : sig{nil_sig};;

rule kind_sig 'S : sig{'S[nil_sig]} -->
    sequent { 'S >> 'K } -->
    sig{'S[hyp{'K; a. nil_sig}]};;

rule type_sig 'S : sig{'S[nil_sig]} -->
   sequent { 'S >> mem{'A; type} } -->
   sig{'S[hyp{'A; c. nil_sig}]};;

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
