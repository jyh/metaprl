(*
 * Explains IR.
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
extends M_doc_comment

declare math_AddOp
declare math_SubOp
declare math_MulOp
declare math_DivOp

declare math_LtOp
declare math_LeOp
declare math_EqOp
declare math_NeqOp
declare math_GeOp
declare math_GtOp

declare math_AtomFalse
declare math_AtomTrue
declare math_AtomInt[i:s]
declare math_AtomBinop{'op; 'a1; 'a2}
declare math_AtomRelop{'op; 'a1; 'a2}
declare math_AtomFun{'x; 'e}
declare math_AtomVar{'v}
declare math_AtomFunVar{'R; 'v}

declare math_LetAtom{'a; 'v; 'e['v]}
declare math_If{'a; 'e1; 'e2}

declare math_ArgNil
declare math_ArgCons{'a; 'rest}
declare math_TailCall{'f; 'args}

declare math_Length[i:s]
declare math_AllocTupleNil
declare math_AllocTupleCons{'a; 'rest}
declare math_LetTuple{'length; 'tuple; 'v; 'e['v]}
declare math_LetSubscript{'a1; 'a2; 'v; 'e['v]}
declare math_SetSubscript{'a1; 'a2; 'a3; 'e}

declare math_LetApply{'f; 'a; 'v; 'e['v]}
declare math_LetClosure{'a1; 'a2; 'f; 'e['f]}
declare math_Return{'a}

declare math_LetRec{'R; 'e1; 'e2}
declare math_LetRec{'R; 'e1}
declare math_Fields{'fields}
declare math_Label[tag:t]
declare math_FunDef{'label; 'exp; 'rest}
declare math_FunDef{'label; 'exp}
declare math_EndDef
declare math_LetFun{'R; 'label; 'f; 'e}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
