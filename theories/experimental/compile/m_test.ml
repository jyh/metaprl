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
interactive fib_prog 'H :
   sequent [m] { 'H; cont: exp >- compilable{
      LetRec{R.
         FunDef{Label["fib":t]; AtomFun{i.
            LetFun{'R; Label["fib":t]; fib.
            If{AtomBinop{LeOp; 'i; AtomInt[1:n]};
               Return{'i};

               LetApply{'fib; AtomBinop{SubOp; 'i; AtomInt[1:n]}; v1.
               LetApply{'fib; AtomBinop{SubOp; 'i; AtomInt[2:n]}; v2.
               Return{AtomBinop{AddOp; 'v1; 'v2}}}}}}};
         EndDef};
      R. LetFun{'R; Label["fib":t]; fib.
         TailCall{'fib; AtomInt[35:n]}}}} }

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
