(*
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003 Adam Granicz, Caltech
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
 * Author: Adam Granicz
 * @email{granicz@cs.caltech.edu}
 * @end[license]
 *)
extends Unity_theory

interactive test_prog :
   sequent { >-
      Program["simple"]{
         Declare{TyInt{DummyPos}; DummyPos; x.
         Declare{TyInt{DummyPos}; DummyPos; y.
         Declare{TyInt{DummyPos}; DummyPos; z.
         Declare{TyInt{DummyPos}; DummyPos; sum.
         Declare{TyArray{TyInt{DummyPos}; IntExp[10:n]{DummyPos}; DummyPos}; DummyPos; a.
         Identity{VarExp{'sum; DummyPos}; IntExp[10:n]{DummyPos}; DummyPos;
         Body{
            Statement{
               UCons{VarExp{'x; DummyPos}; UCons{VarExp{'y; DummyPos}; UNil}};
               UCons{IntExp[1]{DummyPos}; UCons{IntExp[2]{DummyPos}; UNil}}; DummyPos;
            Statement{VarExp{'z; DummyPos}; IntExp[2]{DummyPos}; DummyPos;
            StatementSkip}};
            Statement{
               UCons{VarExp{'x; DummyPos}; UNil};
               UCons{IntExp[11]{DummyPos}; UNil};
               BinopExp{NeqOp; VarExp{'x; DummyPos}; IntExp[10:n]{DummyPos}; DummyPos};
               DummyPos;
            Statement{
               UCons{SubscriptExp{VarExp{'a; DummyPos}; VarExp{'x; DummyPos}; DummyPos}; UNil};
               UCons{IntExp[5]{DummyPos}; UNil};
               DummyPos;
               StatementSkip}}}}}}}}};
         DummyPos} }
