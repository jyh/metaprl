doc <:doc<
   @begin[spelling]
   @end[spelling]

   @module[UNITY]
   This module defines a UNITY abstract syntax.

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2003 Adam Granicz, Caltech

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

   Author: Adam Granicz
   @email{granicz@cs.caltech.edu}
   @end[license]
>>
extends Base_theory

declare AddOp
declare SubOp
declare MulOp
declare DivOp

declare LtOp
declare LeOp
declare EqOp
declare NeqOp
declare GeOp
declare GtOp

declare TyInt{'pos}
declare TyArray{'array; 'size; 'pos}

declare TrueExp{'pos}
declare FalseExp{'pos}
declare VarExp{'v; 'pos}
declare IntExp[i:n]{'pos}
declare BinopExp{'op; 'e1; 'e2; 'pos}
declare SubscriptExp{'e1; 'e2; 'pos}
declare ApplyExp{'f; 'args; 'pos}

declare Body{'inits; 'assigns}

declare Declare{'ty; 'pos; v. 'rest['v]}
declare Identity{'e1; 'e2; 'pos; 'rest}

declare Statement{'lvalues; 'values; 'pos; 'next}
declare Statement{'lvalues; 'values; 'cond; 'pos; 'next}
declare Statement{'range; 'cond; 'pos; 'assign; 'next}
declare StatementSkip

declare Program[name:s]{'program; 'pos}

declare DummyPos

declare UCons{'el; 'list}
declare UNil

declare unity

doc docoff

