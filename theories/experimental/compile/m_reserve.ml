(*
 * Add reserve instructions.
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

open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Top_conversionals

(*
 * Helper to rever argument list.
 *)
declare reverse_args{'args}
declare reverse_args{'dst; 'src}

prim_rw unfold_reverse_args :
   reverse_args{'args}
   <-->
   reverse_args{ArgNil; 'args}

prim_rw reverse_args_cons :
   reverse_args{'dst; ArgCons{'a; 'rest}}
   <-->
   reverse_args{ArgCons{'a; 'dst}; 'rest}

prim_rw reverse_args_nil :
   reverse_args{'args; ArgNil}
   <-->
   'args

(*
 * Add a reserve before each tailcall.
 *)
prim_rw add_reserve :
   TailCall{'f; 'args}
   <-->
   Reserve[0:n]{TailCall{'f; 'args}}

(*
 * Function parameters.
 *)
declare ReserveParams{'params; 'e}

prim_rw add_reserve_params :
   AtomFun{v. 'e['v]}
   <-->
   ReserveParams{ArgNil; AtomFun{v. 'e['v]}}

prim_rw add_reserve_param :
   ReserveParams{'params; AtomFun{v. 'e['v]}}
   <-->
   AtomFun{v. ReserveParams{ArgCons{AtomVar{'v}; 'params}; 'e['v]}}

prim_rw reserve_params :
   ReserveParams{'params; Reserve[words:n]{'e}}
   <-->
   Reserve[words:n]{reverse_args{'params}; 'e}

(*
 * Need an extra form for arithmetic.
 *)
declare Reserve{'words; 'e}

prim_rw reduce_reserve :
   Reserve{number[words:n]; 'e}
   <-->
   Reserve[words:n]{'e}

(*
 * Propagate the reserve up the expression.
 *)
prim_rw reserve_let_atom :
   LetAtom{'a; v. Reserve[words:n]{'e['v]}}
   <-->
   Reserve[words:n]{LetAtom{'a; v. 'e['v]}}

prim_rw reserve_if :
   If{'a; Reserve[words1:n]{'e1}; Reserve[words2:n]{'e2}}
   <-->
   Reserve{max{number[words1:n]; number[words2:n]}; If{'a; 'e1; 'e2}}

prim_rw reserve_let_tuple :
   LetTuple{Length[i:n]; 'tuple; v. Reserve[words:n]{'e['v]}}
   <-->
   Reserve{add{add{number[i:n]; number[1:n]}; number[words:n]};
           LetTuple{Length[i:n]; 'tuple; v. 'e['v]}}

prim_rw reserve_let_subscript :
   LetSubscript{'a1; 'a2; v. Reserve[words:n]{'e['v]}}
   <-->
   Reserve[words:n]{LetSubscript{'a1; 'a2; v. 'e['v]}}

prim_rw reserve_set_subscript :
   SetSubscript{'a1; 'a2; 'a3; Reserve[words:n]{'e}}
   <-->
   Reserve[words:n]{SetSubscript{'a1; 'a2; 'a3; 'e}}

prim_rw reserve_reserve :
   Reserve[words1:n]{Reserve[words2:n]{'e}}
   <-->
   Reserve{add{number[words1:n]; number[words2:n]}; 'e}

prim_rw reserve_let_closure :
   LetClosure{'a1; 'a2; f. Reserve[words:n]{'e['f]}}
   <-->
   Reserve{add{number[words:n]; number[3:n]}; LetClosure{'a1; 'a2; f. 'e['f]}}

(*
 * Add function parameters.
 *)
declare r

(*! @docoff *)

let resource reduce +=
   [<< ReserveParams{'params; AtomFun{v. 'e['v]}} >>, add_reserve_param;
    << Reserve{number[words:n]; 'e} >>, reduce_reserve;
    << LetAtom{'a; v. Reserve[words:n]{'e['v]}} >>, reserve_let_atom;
    << If{'a; Reserve[words1:n]{'e1}; Reserve[words2:n]{'e2}} >>, reserve_if;
    << LetTuple{Length[i:n]; 'tuple; v. Reserve[words:n]{'e['v]}} >>, reserve_let_tuple;
    << LetSubscript{'a1; 'a2; v. Reserve[words:n]{'e['v]}} >>, reserve_let_subscript;
    << SetSubscript{'a1; 'a2; 'a3; Reserve[words:n]{'e}} >>, reserve_set_subscript;
    << Reserve[words1:n]{Reserve[words2:n]{'e}} >>, reserve_reserve;
    << LetClosure{'a1; 'a2; f. Reserve[words:n]{'e['f]}} >>, reserve_let_closure;
    << Reserve{number[words:n]; 'e} >>, reduce_reserve;
    << reverse_args{'args} >>, unfold_reverse_args;
    << reverse_args{'dst; ArgCons{'a; 'rest}} >>, reverse_args_cons;
    << reverse_args{'args; ArgNil} >>, reverse_args_nil]

(*
 * Add reservations.
 *)
let reserveT =
   rwh add_reserve 0
   thenT rwh add_reserve_params 0
   thenT rw reduceC 0
   thenT rw (repeatC (higherC reserve_params)) 0

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
