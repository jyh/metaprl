doc <:doc< -*- mode: text; -*-
   @begin[spelling]
   YACC lexing params LetAtom op lexer regex LALR pos
   EQ ID exp
   @end[spelling]
  
   @begin[doc]
   @section[m_doc_parsing]{Parsing}
   @docoff
   @end[doc]
  
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
  
   @docoff
>>
extends M_doc_ir

doc <:doc< 
@begin[doc]

In order to use the formal system for program transformation,
source-level programs expressed as sequences of characters must first
be translated into a term representation for use in the @MetaPRL
framework.  We assume that the source language can be specified using
a context-free grammar, and traditional lexing and parsing methods can
be used to perform the translation.

@MetaPRL provides these capabilities using the integrated Phobos
@cite["GH02"] generic lexer and parser, which enables users to specify
parts of their logical theories using their own notation.  For
instance, we can use actual program notation (instead of the uniform
term syntax) to express program transformations in rewrite rules and
we can specify test programs in source notation.

@begin[figure,syntax]
$$
@begin[array,rcll]
@line{@it{op} {::=}   {+ @pipe - @pipe * @pipe /} @hbox{Binary operators}}
@line{{}      {@pipe} {= @pipe <> @pipe < @pipe @le @pipe > @pipe @ge} {}}
@line{{} {} {} {}}
@line{@it{e} {::=} {@AtomTrue @pipe @AtomFalse} @hbox{@it{Booleans}}}
@line{{} {@pipe} @AtomInt[i] @hbox{@it{Integers}}}
@line{{} {@pipe} v @hbox{@it{Variables}}}
@line{{} {@pipe} {e @space @it{op} @space e} @hbox{@it{Binary expressions}}}
@line{{} {@pipe} @AtomFun{v; e} @hbox{@it{Anonymous functions}}}
@line{{} {@pipe} @If{e; e; e} @hbox{@it{Conditionals}}}
@line{{} {@pipe} {e[e]} @hbox{@it{Subscripting}}}
@line{{} {@pipe} {e[e] @leftarrow e} @hbox{@it{Assignment}}}
@line{{} {@pipe} {e; e} @hbox{@it{Sequencing}}}
@line{{} {@pipe} {e(e_1, @ldots, e_n)} @hbox{@it{Application}}}
@line{{} {@pipe} @LetAtom{e; v; e} @hbox{@it{Let definitions}}}
@line{{} {@pipe} {@xlet @xrec f_1 (v_1, @ldots, v_n) = e} @hbox{@it{Recursive functions}}}
@line{{} {} @ldots {}}
@line{{} {} {@xand f_n (v_1, @ldots, v_n) = e}}
@end[array]
$$
@caption{Program syntax}
@end[figure]

A Phobos language specification resembles a typical parser definition
in YACC @cite[Joh75], except that semantic actions for productions use
term rewriting.  Phobos employs @emph{informal} rewriting, which means
that it uses a rewriting engine that can create new variable bindings
and perform capturing substitution.

In Phobos, the lexer for a language is specified as a set of lexical
rewrite rules of the form $@it{regex} @longleftrightarrow @it{term}$,
where $@it{regex}$ is a special term that is created for every token
and contains the matched input as a string parameter as well as a
subterm containing the position in the source text, which can be used
to produce more informative messages if an error is detected.  The
following example demonstrates a single lexer clause, that translates
a nonnegative decimal number to a term with operator name @tt{number} and a
single integer parameter.

$$
@tt["NUM = \"[0-9]+\""] @space @lbrace @bf[token][i] @lbrace pos @rbrace @longleftrightarrow number[i] @rbrace
$$

The parser is defined as a set of grammar productions. For each
grammar production in the program syntax shown in Figure
@reffigure[syntax], we define a production in the form

$$
S ::= S_1 @ldots S_n @longleftrightarrow term
$$

where the symbols $S_i$ may be annotated with a term pattern. For
instance, the production for the let-expression is defined with the
following production and semantic action.

$$
@begin[array,l]
   @line{@tt{exp ::= LET @space ID@left["<"] v @right[">"] @space EQ @space exp@left["<"] e @right[">"] @space IN @space exp@left["<"] rest @right[">"]}}
   @line{{@longleftrightarrow @LetAtom{e; v; rest}}}
@end[array]
$$

Phobos constructs an LALR(1) parser from these specifications that
maintains a stack of terms and applies the associated rewrite rule
each time a production is reduced by replacing the corresponding terms
on the stack with the result. For the parser to accept, the stack must
contain a single term corresponding to the start symbol of the
grammar.

It may not be feasible during parsing to create the initial binding structure of the programs.  For
instance, in our implementation function parameters are collected as a list and are not initially
bound in the function body. Furthermore, for mutually recursive functions, the function variables
are not initially bound in the functions' bodies.  For this reason, the parsing phases is usually
followed by an additional rewrite phase that performs these operations using the informal rewriting
engine.  The source text is replaced with the resulting term on completion.

@docoff
@end[doc]
>>

(*
 * -*-
 * Local Variables:
 * fill-column: 100
 * End:
 * -*-
 *)
