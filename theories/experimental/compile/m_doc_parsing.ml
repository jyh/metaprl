(* -*- mode: text; -*- *)
doc <:doc<
   @begin[spelling]
   YACC lexing params LetAtom op lexer regex LALR pos
   EQ ID exp
   @end[spelling]

   @section[m_doc_parsing]{Language}

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2003 Jason Hickey, Caltech

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

   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
   @end[license]
>>
extends M_doc_ir

doc <:doc<

The abstract syntax of the language of our compiler is shown in Figure @reffigure[syntax]. In order
to use the formal system for program transformation, the concrete syntax of the source-level
programs must first be translated into a term representation for use in the @MetaPRL framework. We
achieve that by using the Phobos @cite["GH02"] extensible lexer and parser, which is a part of the
framework.  A Phobos language specification resembles a typical parser definition in YACC
@cite[Joh75], except that semantic actions for productions use the @MetaPRL term rewriting engine.

@begin[figure,syntax]
$$
@begin[array,rcll]
@line{@it{op} {::=}   {+ @vbar - @vbar * @vbar /} @hbox{Binary operators}}
@line{{}      {@pipe} {= @pipe <> @pipe < @pipe @le @pipe > @pipe @ge} {}}
@line{{} {} {} {}}
@line{@it{e} {::=} {@AtomTrue @vbar @AtomFalse} @hbox{Booleans}}
@line{{} {@pipe} @AtomInt[i] @hbox{Integers}}
@line{{} {@pipe} v @hbox{Variables}}
@line{{} {@pipe} {e @space @it{op} @space e @space} @hbox{Binary expressions}}
@line{{} {@pipe} @AtomFun{v; e} @hbox{Anonymous functions}}
@line{{} {@pipe} @If{e; e; e} @hbox{Conditionals}}
@line{{} {@pipe} {e.[e]} @hbox{Subscripting}}
@line{{} {@pipe} {e.[e] @leftarrow e} @hbox{Assignment}}
@line{{} {@pipe} {e; e} @hbox{Sequencing}}
@line{{} {@pipe} {e(e, @ldots, e)} @hbox{Application}}
@line{{} {@pipe} @LetAtom{e; v; e} @hbox{Let definitions}}
@line{{} {@pipe} {@xlet @xrec f_1 (v, @ldots, v) = e} @hbox{Recursive functions}}
@line{{} {} @vdots {}}
@line{{} {} {@xand f_n (v, @ldots, v) = e}}
@end[array]
$$
@caption{Program syntax}
@end[figure]

@docoff
>>

(*
 * -*-
 * Local Variables:
 * fill-column: 100
 * End:
 * -*-
 *)
