(*
 * Test file.
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
extends M_theory

(************************************************************************
 * Just for testing.
 *)
interactive test_prog 'H :
   sequent [m] { 'H; cont: exp >- compilable{CPS{AtomVar{'cont};
                                  LetAtom{AtomInt[1:n]; v1.
                                  LetAtom{AtomBinop{AddOp; AtomVar{'v1}; AtomInt[3]}; v2.
                                  FunDecl{f.
                                  FunDef{'f; AtomFun{v3.
                                     LetPair{AtomVar{'v2}; AtomVar{'v3}; v4.
                                     LetPair{AtomVar{'v1}; AtomVar{'v4}; v5.
                                     LetSubscript{AtomVar{'v5}; AtomInt[0:n]; v6.
                                     Return{AtomVar{'v6}}}}}};
                                  TailCall{AtomFunVar{'f}; AtomInt[17]}}}}}}}
               }

interactive fib_prog 'H :
   sequent [m] { 'H; cont: exp >- compilable{CPS{AtomVar{'cont};
      FunDecl{fib.
      FunDef{'fib; AtomFun{i.
         If{AtomBinop{LeOp; AtomVar{'i}; AtomInt[1:n]};
            Return{AtomVar{'i}};
            LetApply{AtomFunVar{'fib}; AtomBinop{SubOp; AtomVar{'i}; AtomInt[1:n]}; v1.
               LetApply{AtomFunVar{'fib}; AtomBinop{SubOp; AtomVar{'i}; AtomInt[2:n]}; v2.
               Return{AtomBinop{AddOp; AtomVar{'v1}; AtomVar{'v2}}}}}}};
      TailCall{AtomFunVar{'fib}; AtomInt[35:n]}}}}} }

(*
interactive ext_test_prog 'H :
   sequent [m] { 'H >- compilable{.<:ext<
                          let v1 = 1 in
                          let v2 = 2+v1 in
                          let f (v3) =
                             let v4 = (v2, v3) in
                             let v5 = v4[0] in
                                v5
                          in
                             f(17)>>} }
*)

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
