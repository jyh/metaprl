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

extends Lf_sig;;

declare dfun{'A. x. 'K['x]};;
declare lambda{'A; x. 'B['x]};;
declare apply{'A; 'B};;

(*
 * Beta reduction.
 *)
rewrite beta : lambda{'A; x. 'M['x]} 'N <--> 'M['N];;

(*
 * Kinding judgement.
 *)
rule pi_kind 'S 'C : sequent { <S>; <C>; x. 'A >- 'K['x] } -->
   sequent { <S>; <C> >- x: 'A -> 'K['x] };;

(*
 * Typehood.
 *)
rule pi_fam 'S 'C :
   sequent { <S>; <C>; x. 'A >- mem{'B['x]; type} } -->
   sequent { <S>; <C> >- mem{x: 'A -> 'B['x]; type } };;

(*
 * Membership.
 *)
rule pi_abs_fam 'S 'C :
   sequent { <S>; <C>; x. 'A >- mem{'B['x]; 'K['x]} } -->
   sequent { <S>; <C> >- mem{lambda{'A; x. 'B['x]}; y: 'A -> 'K['y] } };;

(*
 * Abs elimination.
 *)
rule pi_app_fam 'S 'C (x: 'B -> 'K['x]) :
   sequent { <S>; <C> >- mem{'A; x: 'B -> 'K['x] } } -->
   sequent { <S>; <C> >- mem{'M; 'B} } -->
   sequent { <S>; <C> >- mem{'A 'M; 'K['M] } };;

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
