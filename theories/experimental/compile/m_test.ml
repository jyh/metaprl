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
interactive fib_prog :
   sequent { <H> >- compilable{
      LetAtom{AtomInt[1:n]; one.
      LetAtom{AtomInt[2:n]; two.
      LetRec{R. Fields{
         FunDef{Label["fib":t]; AtomFun{i.
            LetFun{'R; Label["fib":t]; fib.
            If{AtomRelop{LeOp; AtomVar{'i}; AtomInt[1:n]};
               Return{AtomVar{'i}};

               LetApply{AtomVar{'fib}; AtomBinop{SubOp; AtomVar{'i}; AtomVar{'one}}; v1.
               LetApply{AtomVar{'fib}; AtomBinop{SubOp; AtomVar{'i}; AtomVar{'two}}; v2.
               Return{AtomBinop{AddOp; AtomVar{'v1}; AtomVar{'v2}}}}}}}};
         EndDef}};
      R. LetFun{'R; Label["fib":t]; fib.
         TailCall{AtomVar{'fib}; ArgCons{AtomInt[35:n]; ArgNil}}}}}}} }

interactive fib_prog2 :
   sequent { <H> >- compilable{
      LetRec{R. Fields{
         FunDef{Label["fib":t]; AtomFun{i.
            LetFun{'R; Label["fib":t]; fib.
            If{AtomRelop{LeOp; AtomVar{'i}; AtomInt[1:n]};
               Return{AtomVar{'i}};

               LetApply{AtomVar{'fib}; AtomBinop{SubOp; AtomVar{'i}; AtomInt[1:n]}; v1.
               LetApply{AtomVar{'fib}; AtomBinop{SubOp; AtomVar{'i}; AtomInt[2:n]}; v2.
               Return{AtomBinop{AddOp; AtomVar{'v1}; AtomVar{'v2}}}}}}}};
         EndDef}};
      R. LetFun{'R; Label["fib":t]; fib.
         TailCall{AtomVar{'fib}; ArgCons{AtomInt[25:n]; ArgNil}}}}} }

(*
 * This is a program that should have some spills.
 *)
interactive spill_prog :
   sequent { <H> >- compilable{
      LetRec{R. Fields{
         FunDef{Label["spill":t]; AtomFun{i.
            LetAtom{AtomBinop{AddOp; AtomVar{'i}; AtomInt[1:n]}; i1.
            LetAtom{AtomBinop{AddOp; AtomVar{'i}; AtomInt[2:n]}; i2.
            LetAtom{AtomBinop{AddOp; AtomVar{'i}; AtomInt[3:n]}; i3.
            LetAtom{AtomBinop{AddOp; AtomVar{'i}; AtomInt[4:n]}; i4.
            LetAtom{AtomBinop{AddOp; AtomVar{'i}; AtomInt[5:n]}; i5.
            LetAtom{AtomBinop{AddOp; AtomVar{'i}; AtomInt[6:n]}; i6.
            LetAtom{AtomBinop{AddOp; AtomVar{'i}; AtomInt[7:n]}; i7.
            Return{AtomBinop{AddOp; AtomVar{'i1};
                   AtomBinop{AddOp; AtomVar{'i2};
                   AtomBinop{AddOp; AtomVar{'i3};
                   AtomBinop{AddOp; AtomVar{'i4};
                   AtomBinop{AddOp; AtomVar{'i5};
                   AtomBinop{AddOp; AtomVar{'i6}; AtomVar{'i7}}}}}}}}}}}}}}}};
         EndDef}};
      R. LetFun{'R; Label["spill":t]; spill.
         TailCall{AtomVar{'spill}; ArgCons{AtomInt[25:n]; ArgNil}}}}} }


(*
interactive ext_fib_prog2 :
   sequent { <H> >- compilable{.
      <:ext<
         let rec fib (i) =
            if i < 1 then
               i
            else
               let v1 = fib (i - 1) in
               let v2 = fib (i - 2) in
                  v1 + v2
         in
            fib (25) >>} }
*)

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
