(*!
 * @begin[spelling]
 * args centermath defrule hyps mathop
 * rulebox tac verbatim typeset
 * @end[spelling]
 *
 * @begin[doc]
 * @module[Comment]
 *
 * The @tt{Comment} module defines @emph{structured} comments.
 * Structured comments begin with the sequence @tt{({*}!}.  They
 * are usually used to provide documentation, although special forms
 * can be defined for other purposes.
 *
 * Currently, structured comments can be used only at the top level of
 * of an interface or implementation.  The text in the comment is parsed
 * into a sequence of strings in a list.  The text can also
 * contain terms, which begin with the @tt{@@} character.
 *
 * @begin[verbatim]
 * @opname[s1, ..., sm]{t1; ...; tn},
 * @end[verbatim]
 *
 * The @tt[opname] is an operator name.  The usual quantification can be
 * used; the term @code{@Itt_dprod!prod} refers to the @hrefterm[prod] term
 * defined in the @hrefmodule[Itt_dprod] module.  The strings $s_1, @ldots, s_m$
 * are the @emph{parameters} of the term, and the $t_1; @cdots; t_n$ expressions
 * are the subterms.  The parameters must be strings, possibly enclosed in
 * double-quotes.  The subterms are normal comment text.
 *
 * Terms can also be constructed using a @tt{begin/end} construction.  For example,
 * the @tt[doc] term encloses a comment that uses a @LaTeX formatting-style.
 *
 * @begin[verbatim]
 * @doc{Hello world}
 * @end[verbatim]
 *
 * The following definition is equivalent.
 *
 * @begin[verbatim]
 * @begin[doc]
 * Hello world.
 * @end[doc]
 * @end[verbatim]
 *
 * There is also a @emph{math} mode, which is entered for terms between
 * @tt["$"] or @tt["$$"] forms.  The contents of math mode is
 * parsed in a similar manner to normal mode, but the `_' and `^' characters
 * are significant in math mode (they are normal text in normal mode).
 * The `_' term identifies a subscript operation, and the `^' term
 * denotes a superscript.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2000 Jason Hickey, Caltech
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
 * Author: Jason Hickey @email{jyh@cs.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
extends Base_dform

(************************************************************************
 * STRUCTURED COMMENTS                                                  *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The @tt[comment_white] term represents white space.
 * The @tt[comment_string] term is a literal string.
 * The @tt[comment_block] term encloses a nested comment
 * block.  The @tt[comment_term] term contains an arbitrary term.
 * @end[doc]
 *)
declare comment_white
declare comment_string[s:s]
declare comment_block{'t}
declare comment_term{'t}

(*!
 * @begin[doc]
 * The @tt[doc] term is used to enclose documentation blocks,
 * usually with the following type of definition.
 *
 * @begin[verbatim]
 * @begin[doc]
 * text
 * @end[doc]
 * @end[verbatim]
 *
 * The @tt[license] term is used to enclose the license agreement
 * text for a module.
 *
 * All the words in the @tt[spelling] term are added to the
 * spelling dictionary as correctly-spelled words.
 * @end[doc]
 *)
declare doc{'t}
declare license{'t}
declare spelling{'t}
declare misspelled{'t}
(*! @docoff *)

(*
 * Standard sisplay forms.
 *)
declare com_cbreak
declare com_hbreak

dform com_cbreak_df : mode[tex] :: com_cbreak =
   slot["raw", " "]

dform com_hbreak_df : mode[tex] :: com_hbreak =
   slot["raw", " "]

dform com_cbreak_df : except_mode[tex] :: com_cbreak =
   cbreak["", " "]

dform com_hbreak_df : except_mode[tex] :: com_hbreak =
   hbreak["", " "]

dform comment_string_df1 : comment_string[s:s] =
   slot[s:s]

dform comment_block_df1 : comment_block{'t} =
   't

dform comment_term_df1 : comment_term{'t} =
   't

(*!
 * @begin[doc]
 * The @code{@docoff} term disables display for text that
 * follows the structured comment.  The @code{@begin[doc]} command
 * re-enables display.
 * @end[doc]
 *)
declare docoff
(*! @docoff *)

dform docoff_df1 : mode[tex] :: docoff =
   izone `"\\texoff" ezone

dform docoff_df2 : except_mode[tex] :: docoff =
   bf["docoff"]

(*
 * TeX version.
 *)
declare tex_comment{'t}
declare tex_comment_item{'t}

dform tex_comment_df1 : tex_comment{nil} =
   `""

dform tex_comment_df2 : tex_comment{cons{'h; 't}} =
   tex_comment_item{'h} tex_comment{'t}

dform tex_comment_df2 : tex_comment{comment_term{'t}} =
   tex_comment{'t}

dform tex_comment_item_df1 : tex_comment_item{comment_white} =
   `""

dform tex_comment_item_df2 : tex_comment_item{comment_string[s:s]} =
   `""

dform tex_comment_item_df3 : tex_comment_item{comment_block{'t}} =
   `""

dform tex_comment_item_df4 : tex_comment_item{comment_term{'t}} =
   `""

dform tex_comment_item_df4 : tex_comment_item{comment_term{docoff}} =
   izone slot["raw", "%\n\\end{tabbing}\\fi\\texoff{}%\n\\iftex%\n\\begin{tabbing}%\n"] ezone

dform tex_comment_item_df5 : tex_comment_item{comment_term{doc{'t}}} =
   izone slot["raw", "%\n\\end{tabbing}\\fi\\textrue%\n"] ezone
   't
   izone slot["raw","\\iftex\\begin{tabbing}%\n"] ezone

dform tex_comment_white_df1 : mode[tex] :: comment_white =
   izone slot["raw", " "] ezone

dform tex_comment_white_df2 : mode[tex] :: cons{comment_white; cons{comment_white; 't}} =
   izone slot["raw", "\n\n"] ezone slot{'t}

(*
 * Plain version.
 *)
dform normal_comment_white_df1 : except_mode[tex] :: comment_white =
   com_cbreak

dform normal_comment_white_df2 : except_mode[tex] :: cons{comment_white; cons{comment_white; 't}} =
   com_hbreak slot{'t}

dform normal_doc_df2 : except_mode[tex] :: doc{'t} =
   `"@begin[doc]" com_hbreak 't com_hbreak `"@end[doc]"

dform normal_license_df2 : except_mode[tex] :: license{'t} =
   `"@begin[license]" com_hbreak 't com_hbreak `"@end[license]"

(*
 * Spelling.
 *)
dform spelling_df1 : spelling{'t} =
   `""

dform misspelled_df1 : misspelled{'t} =
   't

(*
 * PRL comments.
 *)
declare prl_comment{'t}

dform prl_comment_df1 : except_mode[tex] :: prl_comment{'t} =
   pushm[" * "] szone `"(*" 't com_hbreak `" *)" ezone popm

(************************************************************************
 * COMMENT ITEMS                                                        *
 ************************************************************************)

(*!
 * @begin[doc]
 * The @code{@theory} term produces a chapter header for a theory (e.g.
 * a collection of modules) and the @code{@module[name:s]} produces a section
 * header for the current module.
 * @end[doc]
 *)
declare "theory"{'t}
declare "module"[name:s]
(*! @docoff *)

dform theory_df1 : mode[tex] :: "theory"{'t} =
   izone `"\\theory{" ezone slot{'t} izone `"}" ezone

dform theory_df2 : except_mode[tex] :: "theory"{'t} =
   com_hbreak bf{'t} com_hbreak com_hbreak

dform module_df1 : mode[tex] :: "module"[name:s] =
   izone `"\\labelmodule{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform module_df2 : except_mode[tex] :: "module"[name:s] =
   com_hbreak bf[name:s] com_hbreak com_hbreak

(*!
 * @begin[doc]
 * Bookmarking commands.
 * @end[doc]
 *)
declare chapter[name:s]{'t}
declare section[name:s]{'t}
declare subsection[name:s]{'t}
declare subsubsection[name:s]{'t}
(*! @docoff *)

dform chapter_df1 : mode[tex] :: "chapter"[name:s]{'t} =
   izone `"\\labelchapter{" slot[name:s] `"}{" ezone slot{'t} izone `"}" ezone

dform chapter_df2 : except_mode[tex] :: "chapter"[name:s]{'t} =
   com_hbreak bf{'t} com_hbreak com_hbreak

dform section_df1 : mode[tex] :: "section"[name:s]{'t} =
   izone `"\\labelsection{" slot[name:s] `"}{" ezone slot{'t} izone `"}" ezone

dform section_df2 : except_mode[tex] :: "section"[name:s]{'t} =
   com_hbreak bf{'t} com_hbreak com_hbreak

dform subsection_df1 : mode[tex] :: "subsection"[name:s]{'t} =
   izone `"\\labelsubsection{" slot[name:s] `"}{" ezone slot{'t} izone `"}" ezone

dform subsection_df2 : except_mode[tex] :: "subsection"[name:s]{'t} =
   com_hbreak bf{'t} com_hbreak com_hbreak

dform subsubsection_df1 : mode[tex] :: "subsubsection"[name:s]{'t} =
   izone `"\\labelsubsubsection{" slot[name:s] `"}{" ezone slot{'t} izone `"}" ezone

dform subsubsection_df2 : except_mode[tex] :: "subsubsection"[name:s]{'t} =
   com_hbreak bf{'t} com_hbreak com_hbreak

(*!
 * @begin[doc]
 * The @code{@modsection} term produces a subsection header.
 * @end[doc]
 *)
declare modsection{'t}
(*! @docoff *)

dform modsection_df1 : mode[tex] :: modsection{'t} =
   izone `"\\modsection{" ezone slot{'t} izone `"}" ezone

dform modsection_df2 : except_mode[tex] :: modsection{'t} =
   com_hbreak bf_begin 't bf_end com_hbreak com_hbreak

(*!
 * @begin[doc]
 * The @code{@modsubsection} term produces a sub-subsection header.
 * @end[doc]
 *)
declare modsubsection{'t}
(*! @docoff *)

dform modsubsection_df1 : mode[tex] :: modsubsection{'t} =
   izone `"\\modsubsection{" ezone slot{'t} izone `"}" ezone

dform modsubsection_df2 : except_mode[tex] :: modsubsection{'t} =
   com_hbreak bf_begin 't bf_end com_hbreak

(*!
 * @begin[doc]
 * Generic targets.
 * @end[doc]
 *)
declare target[name:s]{'t}
declare hreftarget[name:s]
(*! @docoff *)

dform target_df1 : mode[tex] :: target[name:s]{'t} =
   izone `"\\hreflabeltarget{" slot[name:s] `"}{" ezone slot{'t} izone `"}" ezone

dform target_df2 : except_mode[tex] :: target[name:s]{'t} =
   bf{'t}

dform hreftarget_df1 : mode[tex] :: "hreftarget"[name:s] =
   izone `"\\hreflabeltarget{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform hreftarget_df2 : except_mode[tex] :: "hreftarget"[name:s] =
   bf[name:s]

(*!
 * @begin[doc]
 * The following terms generate the @emph{standard} @code{@modsection}
 * headings for the commonly-defined parts of a module.
 * @end[doc]
 *)
declare parents
declare rewrites
declare rules
declare convs
declare tactics
declare resources
declare terms
(*! @docoff *)

dform parents_df1 : parents =
   modsection{comment_string["Parents"]}

dform rewrites_df1 : rewrites =
   modsection{comment_string["Rewrites"]}

dform rules_df1 : rules =
   modsection{comment_string["Rules"]}

dform convs_df1 : convs =
   modsection{comment_string["Conversions"]}

dform tactics_df1 : tactics =
   modsection{comment_string["Tactics"]}

dform resources_df1 : resources =
   modsection{comment_string["Resources"]}

dform terms_df1 : terms =
   modsection{comment_string["Terms"]}

(*!
 * @begin[doc]
 * Structured comments are @emph{hypertext enabled}.  The following
 * terms establish hypertext @emph{targets}.
 * @end[doc]
 *)
declare "term"[name:s]
declare "resource"[name:s]
declare "tactic"[name:s]
declare "conv"[name:s]
declare "rule"[name:s]
declare "rewrite"[name:s]
(*! @docoff *)

dform term_df1 : mode[tex] :: "term"[name:s] =
   izone `"\\labelterm{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform term_df2 : except_mode[tex] :: "term"[name:s] =
   bf[name:s]

dform resource_df1 : mode[tex] :: "resource"[name:s] =
   izone `"\\labelresource{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform resource_df2 : except_mode[tex] :: "resource"[name:s] =
   bf[name:s]

dform tactic_df1 : mode[tex] :: "tactic"[name:s] =
   izone `"\\labeltactic{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform tactic_df2 : except_mode[tex] :: "tactic"[name:s] =
   bf[name:s]

dform conv_df1 : mode[tex] :: "conv"[name:s] =
   izone `"\\labelconv{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform conv_df2 : except_mode[tex] :: "conv"[name:s] =
   bf[name:s]

dform rule_df1 : mode[tex] :: "rule"[name:s] =
   izone `"\\labelrule{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform rule_df1 : mode[tex] :: "rewrite"[name:s] =
   izone `"\\labelrewrite{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform rule_df2 : except_mode[tex] :: "rule"[name:s] =
   bf[name:s]

(*!
 * @begin[doc]
 * The hypertext links are specified with the following terms.
 * @end[doc]
 *)
declare hrefmodule[name:s]
declare hrefterm[name:s]
declare hrefresource[name:s]
declare hrefrewrite[name:s]
declare hreftactic[name:s]
declare hrefconv[name:s]
declare hrefrule[name:s]
(*! @docoff *)

dform hrefmodule_df1 : mode[tex] :: hrefmodule[name:s] =
   izone `"\\hreflabelmodule{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform hrefmodule_df2 : except_mode[tex] :: hrefmodule[name:s] =
   bf[name:s]

dform hrefterm_df1 : mode[tex] :: hrefterm[name:s] =
   izone `"\\hreflabelterm{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform hrefterm_df2 : except_mode[tex] :: hrefterm[name:s] =
   bf[name:s]

dform hrefresource_df1 : mode[tex] :: hrefresource[name:s] =
   izone `"\\hreflabelresource{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform hrefresource_df2 : except_mode[tex] :: hrefresource[name:s] =
   bf[name:s]

dform hrefrewrite_df1 : mode[tex] :: hrefrewrite[name:s] =
   izone `"\\hreflabelrewrite{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform hrefrewrite_df2 : except_mode[tex] :: hrefrewrite[name:s] =
   bf[name:s]

dform hreftactic_df1 : mode[tex] :: hreftactic[name:s] =
   izone `"\\hreflabeltactic{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform hreftactic_df2 : except_mode[tex] :: hreftactic[name:s] =
   bf[name:s]

dform hrefconv_df1 : mode[tex] :: hrefconv[name:s] =
   izone `"\\hreflabelconv{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform hrefconv_df2 : except_mode[tex] :: hrefconv[name:s] =
   bf[name:s]

dform hrefrule_df1 : mode[tex] :: hrefrule[name:s] =
   izone `"\\hreflabelrule{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform hrefrule_df2 : except_mode[tex] :: hrefrule[name:s] =
   bf[name:s]

(*!
 * @begin[doc]
 * The @emph{references} print section number of the target in
 * a hypertext link.
 * @end[doc]
 *)
declare refchapter[name:s]
declare refsection[name:s]
declare refsubsection[name:s]
declare refsubsubsection[name:s]

declare refmodule[name:s]
declare refterm[name:s]
declare refresource[name:s]
declare refrewrite[name:s]
declare reftactic[name:s]
declare refconv[name:s]
declare refrule[name:s]
declare reffigure[name:s]
(*! @docoff *)

dform refchapter_df1 : mode[tex] :: refchapter[name:s] =
   izone `"\\reflabelchapter{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform refchapter_df2 : except_mode[tex] :: refchapter[name:s] =
   bf[name:s]

dform refsection_df1 : mode[tex] :: refsection[name:s] =
   izone `"\\reflabelsection{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform refsection_df2 : except_mode[tex] :: refsection[name:s] =
   bf[name:s]

dform refsubsection_df1 : mode[tex] :: refsubsection[name:s] =
   izone `"\\reflabelsubsection{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform refsubsection_df2 : except_mode[tex] :: refsubsection[name:s] =
   bf[name:s]

dform refsubsubsection_df1 : mode[tex] :: refsubsubsection[name:s] =
   izone `"\\reflabelsubsubsection{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform refsubsubsection_df2 : except_mode[tex] :: refsubsubsection[name:s] =
   bf[name:s]

dform refmodule_df1 : mode[tex] :: refmodule[name:s] =
   izone `"\\reflabelmodule{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform refmodule_df2 : except_mode[tex] :: refmodule[name:s] =
   bf[name:s]

dform refterm_df1 : mode[tex] :: refterm[name:s] =
   izone `"\\reflabelterm{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform refterm_df2 : except_mode[tex] :: refterm[name:s] =
   bf[name:s]

dform refresource_df1 : mode[tex] :: refresource[name:s] =
   izone `"\\reflabelresource{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform refresource_df2 : except_mode[tex] :: refresource[name:s] =
   bf[name:s]

dform refrewrite_df1 : mode[tex] :: refrewrite[name:s] =
   izone `"\\reflabelrewrite{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform refrewrite_df2 : except_mode[tex] :: refrewrite[name:s] =
   bf[name:s]

dform reftactic_df1 : mode[tex] :: reftactic[name:s] =
   izone `"\\reflabeltactic{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform reftactic_df2 : except_mode[tex] :: reftactic[name:s] =
   bf[name:s]

dform refconv_df1 : mode[tex] :: refconv[name:s] =
   izone `"\\reflabelconv{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform refconv_df2 : except_mode[tex] :: refconv[name:s] =
   bf[name:s]

dform refrule_df1 : mode[tex] :: refrule[name:s] =
   izone `"\\reflabelrule{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform refrule_df2 : except_mode[tex] :: refrule[name:s] =
   bf[name:s]

dform reffigure_df1 : mode[tex] :: reffigure[name:s] =
   izone `"\\reffigure{" slot[name:s] `"}{" ezone slot[name:s] izone `"}" ezone

dform reffigure_df2 : except_mode[tex] :: reffigure[name:s] =
   bf[name:s]

(*
 * TeX structuring.
 *)
declare "begin"[name:s]
declare "end"[name:s]

dform begin_df1 : mode[tex] :: "begin"[name:s] =
   izone `"\\begin{" slot[name:s] `"}" ezone

dform begin_df2 : except_mode[tex] :: "begin"[name:s] =
   `""

dform end_df1 : mode[tex] :: "end"[name:s] =
   izone `"\\end{" slot[name:s] `"}" ezone

dform end_df2 : except_mode[tex] :: "end"[name:s] =
   `""

(*!
 * @begin[doc]
 * The @code{@noindent} term specifies that the following paragraph
 * should not include the usual indentation for the first line.
 * @end[doc]
 *)
declare noindent
(*! @docoff *)

dform noindent_df1 : mode[tex] :: noindent =
   izone `"\\noindent{}" ezone

dform noindent_df2 : except_mode[tex] :: noindent =
   `""

(*!
 * @begin[doc]
 * The @code{@cite} term represents a @emph{citation}.  The citation
 * only has effect on @LaTeX display mode.
 * @end[doc]
 *)
declare cite[s:s]
(*! @docoff *)

dform cite_df1 : mode[tex] :: cite[text:s] =
   izone `"\\cite{" slot[text:s] `"}" ezone

dform cite_df2 : except_mode[tex] :: cite[text:s] =
   `"cite{" slot[text:s] `"}"

(*!
 * @begin[doc]
 * The following terms display standard representations
 * of the usual names.  @code{@MetaPRL} displays as @MetaPRL;
 * @code{@Nuprl} displays as @Nuprl; @code{@NuPRL} displays as @NuPRL;
 * @code{@OCaml} displays as @OCaml; and @code{@LaTeX} displays as
 * @LaTeX.
 * @end[doc]
 *)
declare "MetaPRL"
declare "Nuprl"
declare "NuPRL"
declare "OCaml"
declare "LaTeX"
declare "MartinLof"
(*! @docoff *)

dform metaprl_df1 : mode[tex] :: "MetaPRL" =
   izone `"\\MetaPRL{}" ezone

dform metaprl_df2 : except_mode[tex] :: "MetaPRL" =
   it["MetaPRL":s]

dform metaprl_df1 : mode[tex] :: "MartinLof" =
   izone `"\\MartinLof{}" ezone

dform metaprl_df2 : except_mode[tex] :: "MartinLof" =
   it["Martin-Lof":s]

dform nuprl_df1 : mode[tex] :: "Nuprl" =
   izone `"\\Nuprl{}" ezone

dform nuprl_df2 : except_mode[tex] :: "Nuprl" =
   it["Nuprl":s]

dform ocaml_df1 : "OCaml" =
   `"OCaml"

dform latex_df1 : mode[tex] :: "LaTeX" =
   izone `"\\LaTeX{}" ezone

dform latex_df2 : except_mode[tex] :: "LaTeX" =
   `"LaTeX"

(*!
 * @begin[doc]
 * The @code{phantom} term produces white space, equivalent in width
 * to the term being typeset.
 * @end[doc]
 *)
declare phantom{'t}
(*! @docoff *)

dform phantom_df1 : mode[tex] :: phantom{'t} =
   izone `"\\phantom{" slot{'t} `"}" ezone

dform phantom_df2 : except_mode[tex] :: phantom{'t} =
   `" "

(*!
 * @begin[doc]
 * @emph{Math mode} is entered with the @code{$text$} and @code{$$text$$}
 * forms.  The @code{$text$} form produces a @tt{math} term, and the
 * @code{$$text$$} form produces a @tt{centermath} term.
 * @end[doc]
 *)
declare math[s:s]
declare math{'t}
declare centermath[s:s]
declare centermath{'t}
(*! @docoff *)

dform math_df1 : math[s:s] = math{slot[s:s]}

dform math_df2 : mode[tex] :: math{'t} =
   izone `"$" ezone slot{'t} izone `"$" ezone

dform math_df3 : except_mode[tex] :: math{'t} =
   `"$" it{'t} `"$"

dform centermath_df1 : centermath[s:s] = centermath{slot[s:s]}

dform centermath_df2 : mode[tex] :: centermath{'t} =
   izone `"$$" ezone slot{'t} izone `"$$" ezone

dform centermath_df3 : except_mode[tex] :: centermath{'t} =
   com_hbreak `"$$" it{'t} `"$$" com_hbreak

(*!
 * @begin[doc]
 * The @code{@code} form produces literal text.
 * The literal text is enclosed in curly brackets.
 * @end[doc]
 *)
declare code[text:s]
(*! @docoff *)

dform code_df1 : mode[tex] :: code[s:s] =
   izone `"\\verb}" slot[s:s] `"}" ezone

dform code_df2 : except_mode[tex] :: code[s:s] =
   tt[s:s]

(*!
 * @begin[doc]
 * The @tt[verbatim] term encloses a block of verbatim text.
 * @end[doc]
 *)
declare verbatim[text:s]
(*! @docoff *)

dform verbatim_df1 : mode[tex] :: verbatim[s:s] =
   izone `"\\begin{verbatim}\n" slot["raw", s:s] `"\n\\end{verbatim}" ezone

dform verbatim_df2 : except_mode[tex] :: verbatim[s:s] =
   tt[s:s]

(*!
 * @begin[doc]
 * The @code{@email} form is similar to the @code{@code} form,
 * but it is normally used to represent an E-mail address.
 * @end[doc]
 *)
declare email[text:s]
(*! @docoff *)

dform email_df1 : mode[tex] :: email[s:s] =
   izone `"\\verb}" slot[s:s] `"}" ezone

dform email_df2 : except_mode[tex] :: email[s:s] =
   tt[s:s]

(*!
 * @begin[doc]
 * Text can be centered with the @code{@center} form.
 * The usual usage is as a begin/end pair.
 *
 * @begin[verbatim]
 * @begin[center]
 * text
 * @end[center]
 * @end[verbatim]
 *
 * Each line of the text in the @tt{center} block is centered.
 * @end[doc]
 *)
declare center{'t}
(*! @docoff *)

dform center_df1 : mode[tex] :: center{'t} =
   izone `"\\begin{center}" ezone 't izone `"\\end{center}" ezone

dform center_df2 : mode[html] :: center{'t} =
   izone `"<center>" ezone 't izone `"</center>" ezone

dform center_df3 : except_mode[tex] :: except_mode[html] :: center{'t} =
   hspace 't hspace

(*!
 * @begin[doc]
 * A block of text can be placed in a figure.
 *
 * @begin[verbatim]
 * @begin[figure,label]
 * text
 * @end[figure]
 * @end[verbatim]
 * @end[doc]
 *)
declare figure[label:s]{'t}
declare caption{'caption}
(*! @docoff *)

dform figure_df1 : mode[tex] :: figure[label:s]{'t} =
   izone `"\\begin{figure}" ezone
   't
   izone `"\\labelfigure{" ezone slot[label:s]
   izone `"}\\end{figure}" ezone

dform figure_df2 : except_mode[tex] :: figure[label:s]{'t} =
   hspace 't hspace

dform caption_df1 : mode[tex] :: caption{'caption} =
   izone `"\\caption{" ezone
   'caption
   izone `"}" ezone

dform caption_df2 : except_mode[tex] :: caption{'caption} =
   `"caption: " slot{'caption}

(*!
 * @begin[doc]
 * Quotations can be centered with the @code{@quote} form.
 * The usual usage is as a begin/end pair.
 *
 * @begin[verbatim]
 * @begin[quote]
 * text
 * @end[quote]
 * @end[verbatim]
 *
 * Each line of the text in the @tt{quote} block is centered.
 * @end[doc]
 *)
declare quote{'t}
declare quotation{'t}
(*! @docoff *)

dform quote_df1 : mode[tex] :: quote{'t} =
   izone `"\\begin{quote}" ezone 't izone `"\\end{quote}" ezone

dform quote_df2 : except_mode[tex] :: quote{'t} =
   hspace 't hspace

dform quotation_df1 : mode[tex] :: quotation{'t} =
   izone `"\\begin{quotation}" ezone 't izone `"\\end{quotation}" ezone

dform quotation_df2 : except_mode[tex] :: quotation{'t} =
   hspace 't hspace

(*!
 * @begin[doc]
 * Footnotes uses the @code{@footnote} form.
 * @end[doc]
 *)
declare footnote{'t}
(*! @docoff *)

dform footnote_df1 : mode[tex] :: footnote{'t} =
   izone `"\\footnote{" ezone 't izone `"}" ezone

dform footnote_df2 : except_mode[tex] :: footnote{'t} =
   hspace 't hspace

(*!
 * @begin[doc]
 * Lists can be declared in three forms.  The @tt{enumerate} form
 * numbers the elements of the list; the @tt{itemize} form places a
 * bullet before each item; and the @tt{description} form takes
 * items that have optional labels.  The @code{@item} form
 * is used to enclose each item in the list.  For example, the
 * following code produces the first four letters of the alphabet
 * preceded by the first four natural numbers (respectively).
 *
 * @begin[verbatim]
 * @begin[enumerate]
 * @item{A}
 * @item{B}
 * @item{C}
 * @item{D}
 * @end[enumerate]
 * @end[verbatim]
 *
 * For the @tt{description} lists, the @code{@item} term
 * takes two arguments; the first is the @emph{label} of the
 * entry, and the second is the @emph{body}.
 * @end[doc]
 *)
declare item{'t}
declare item{'label; 'body}
(*! @docoff *)

dform item_df2 : except_mode[tex] :: item{'t} =
   com_hbreak pushm[3] `"o " 't popm

dform item_df2 : except_mode[tex] :: item{'t1; 't2} =
   com_hbreak pushm[3] `"[" 't1 `"]" 't2 popm

dform item_df1 : mode[tex] :: item{'t} =
   izone `"\\item{}" ezone slot{'t}

dform item_df1 : mode[tex] :: item{'t1; 't2} =
   izone `"\\item[" ezone slot{'t1} izone `"]" ezone slot{'t2}

(*! @doc{ } *)
declare enumerate{'t}
(*! @docoff *)
declare normal_enumerate{'count; 't}

dform enumerate_df2 : except_mode[tex] :: enumerate{'t} =
   normal_enumerate{cons{nil; nil}; 't}

dform normal_enumerate_df1 : normal_enumerate{'count; nil} =
   com_hbreak

dform normal_enumerate_df3 : normal_enumerate{'count; cons{comment_white; 'tl}} =
   normal_enumerate{'count; 'tl}

dform normal_enumerate_df4 : normal_enumerate{'count; cons{comment_term{item{'t}}; 'tl}} =
   com_hbreak pushm[3] df_length{'count} `"." slot{'t} popm
   normal_enumerate{cons{nil; 'count}; 'tl}

dform normal_enumerate_df5 : normal_enumerate{'count; cons{comment_term{item{'t1; 't2}}; 'tl}} =
   com_hbreak pushm[3] slot{'t1} `"." slot{'t2} popm
   normal_enumerate{cons{nil; 'count}; 'tl}

dform enumerate_df1 : mode[tex] :: enumerate{'t} =
   izone `"\\begin{enumerate}" ezone 't izone `"\\end{enumerate}" ezone

(*! @doc{ } *)
declare itemize{'t}
(*! @docoff *)

dform itemize_df1 : mode[tex] :: itemize{'t} =
   izone `"\\begin{itemize}" ezone 't izone `"\\end{itemize}" ezone

dform itemize_df2 : except_mode[tex] :: itemize{'t} =
   't

(*! @doc{ } *)
declare description{'t}
(*! @docoff *)

dform description_df1 : mode[tex] :: description{'t} =
   izone `"\\begin{description}" ezone 't izone `"\\end{description}" ezone

dform description_df2 : except_mode[tex] :: description{'t} =
   normal_enumerate{cons{nil; nil}; 't}

(*! @doc{Other macros} *)
declare lbrace
declare rbrace
declare comment[who:s]{'e}
(*! @docoff *)

dform lbrace_df1 : mode[tex] :: lbrace =
   izone `"\\{" ezone

dform lbrace_df2 : except_mode[tex] :: lbrace =
   "{"

dform rbrace_df1 : mode[tex] :: rbrace =
   izone `"\\}" ezone

dform lbrace_df2 : except_mode[tex] :: rbrace =
   "}"

dform comment_df1 : mode[tex] :: comment[who:s]{'e} =
   izone `"\\comment{" ezone bf[who:s] `": " 'e izone `"}" ezone

dform comment_df2 : except_mode[tex] :: comment[who:s]{'e} =
   szone pushm[3] bf["Comment: "] bf[who:s] hspace 'e popm ezone

(************************************************************************
 * MATH MODE                                                            *
 ************************************************************************)

(*
 * Toplevel form.
 *)
declare math_misspelled{'t}

dform math_misspelled_df1 : math_misspelled{'t} =
   't

(*
 * Allow raw printing.
 *)
declare math_slot[tag:s]{'t}

dform math_slot_df1 : math_slot[tag:s]{'t} =
   slot[tag:s]{'t}

(*!
 * @begin[doc]
 * @modsubsection{Math mode}
 *
 * Terms are formatted in @emph{math mode} if they are
 * placed between matching @tt["$"] symbols (for inline
 * math expressions), or matching @tt["$$"] symbols (for
 * centered math expressions).  All terms in math mode
 * have an @tt[opname] that begins with the prefix @tt{math_}.
 *
 * The following terms define standard forms in math mode.
 *
 * The @tt{math_mathop} and @tt[math_mathrel] terms give their
 * contents the status of an ``operator'' or a ``relation.''  The
 * significance has to do with spacing in math mode.  An operator is
 * always followed by extra white space, and a relation is surrounded
 * by extra white space.
 *
 * The @tt[tt] term displays its contents in a @tt{fixed-width} font;
 * the @tt[bf] term displays the contents in a @bf{bold font}; the
 * @tt[i] and @tt[it] terms display their contents in an
 * @i[italic] font; and the @tt[emph] term @emph{emphasizes} it's
 * contents.
 * @end[doc]
 *)
declare math_mbox{'t}
declare math_hbox{'t}

declare math_mathop{'t}
declare math_mathop[text:s]
declare math_mathrel{'t}
declare math_mathrel[text:s]
declare math_bb{'t}
declare math_bb[text:s]
declare math_tt{'t}
declare math_tt[text:s]
declare math_bf{'t}
declare math_bf[text:s]
declare math_i{'t}
declare math_i[text:s]
declare math_it{'t}
declare math_it[text:s]
declare math_emph{'t}
(*! @docoff *)

dform math_hbox_df1 : mode[tex] :: math_hbox{'t} =
   izone `"\\hbox{" ezone slot{'t} izone `"}" ezone

dform math_hbox_df2 : except_mode[tex] :: math_hbox{'t} =
   slot{'t}

dform math_mbox_df1 : mode[tex] :: math_mbox{'t} =
   izone `"\\mbox{" ezone slot{'t} izone `"}" ezone

dform math_mbox_df2 : except_mode[tex] :: math_mbox{'t} =
   slot{'t}

dform math_mathop_df1 : mode[tex] :: math_mathop{'t} =
   izone `"\\mathop{\\bf " ezone slot{'t} izone `"}" ezone

dform math_mathop_df1 : mode[tex] :: math_mathop[text:s] =
   izone `"\\mathop{\\bf " ezone slot[text:s] izone `"}" ezone

dform math_mathop_df2 : except_mode[tex] :: math_mathop{'t} =
   bf{'t}

dform math_mathop_df2 : except_mode[tex] :: math_mathop[text:s] =
   bf[text:s]

dform math_mathrel_df1 : mode[tex] :: math_mathrel[text:s] =
   izone `"\\mathrel{\\bf " ezone slot[text:s] izone `"}" ezone

dform math_mathrel_df2 : except_mode[tex] :: math_mathrel[text:s] =
   bf[text:s]

dform math_mathrel_df3 : mode[tex] :: math_mathrel{'t} =
   izone `"\\mathrel{\\bf " ezone slot{'t} izone `"}" ezone

dform math_mathrel_df4 : except_mode[tex] :: math_mathrel{'t} =
   bf{'t}

dform math_tt_df1 : mode[tex] :: math_tt{'t} =
   izone `"{\\tt " ezone slot{'t} izone `"}" ezone

dform math_tt_df1 : mode[tex] :: math_tt[text:s] =
   izone `"{\\tt " ezone slot[text:s] izone `"}" ezone

dform math_tt_df2 : except_mode[tex] :: math_tt{'t} =
   tt{'t}

dform math_tt_df2 : except_mode[tex] :: math_tt[text:s] =
   tt[text:s]

dform math_bb_df1 : mode[tex] :: math_bb{'t} =
   izone `"{\\mathbb " ezone slot{'t} izone `"}" ezone

dform math_bb_df1 : mode[tex] :: math_bb[text:s] =
   izone `"{\\mathbb " ezone slot[text:s] izone `"}" ezone

dform math_bb_df2 : except_mode[tex] :: math_bb{'t} =
   bf{'t}

dform math_bb_df2 : except_mode[tex] :: math_bb[text:s] =
   bf[text:s]

dform math_bf_df1 : mode[tex] :: math_bf{'t} =
   izone `"{\\bf " ezone slot{'t} izone `"}" ezone

dform math_bf_df1 : mode[tex] :: math_bf[text:s] =
   izone `"{\\bf " ezone slot[text:s] izone `"}" ezone

dform math_bf_df2 : except_mode[tex] :: math_bf{'t} =
   bf{'t}

dform math_bf_df2 : except_mode[tex] :: math_bf[text:s] =
   bf[text:s]

dform math_i_df1 : mode[tex] :: math_i{'t} =
   izone `"{\\it " ezone slot{'t} izone `"}" ezone

dform math_i_df1 : mode[tex] :: math_i[text:s] =
   izone `"{\\it " ezone slot[text:s] izone `"}" ezone

dform math_i_df2 : except_mode[tex] :: math_i{'t} =
   it{'t}

dform math_i_df2 : except_mode[tex] :: math_i[text:s] =
   it[text:s]

dform math_it_df1 : math_it{'t} =
   math_i{'t}

dform math_it_df2 : math_it[text:s] =
   math_i[text:s]

dform math_emph_df1 : mode[tex] :: math_emph{'t} =
   izone `"{\\it " ezone slot{'t} izone `"}" ezone

dform math_emph_df2 : except_mode[tex] :: math_emph{'t} =
   emph{'t}

(*
 * Math symbols.
 *)
declare math_Type

(*!
 * @begin[doc]
 * The following terms defines some common math symbols.
 *
 * $$
 * @begin[array, lcl]
 * @line{@code{@colon} @equiv @colon}
 * @line{@code{@rightarrow} @equiv @rightarrow}
 * @line{@code{@Rightarrow} @equiv @Rightarrow}
 * @line{@code{@leftarrow} @equiv @leftarrow}
 * @line{@code{@Leftarrow} @equiv @Leftarrow}
 * @line{@code{@leftrightarrow} @equiv @leftrightarrow}
 * @line{@code{@Leftrightarrow} @equiv @Leftrightarrow}
 * @line{@code{@longleftrightarrow} @equiv @longleftrightarrow}
 * @line{@code{@wedge} @equiv @wedge}
 * @line{@code{@vee} @equiv @vee}
 * @line{@code{@phi} @equiv @phi}
 * @line{@code{@cap} @equiv @cap}
 * @line{@code{@cup} @equiv @cup}
 * @line{@code{@bigcap} @equiv @bigcap}
 * @line{@code{@bigcup} @equiv @bigcup}
 * @line{@code{@in} @equiv @in}
 * @line{@code{@cdot} @equiv @cdot}
 * @line{@code{@cdots} @equiv @cdots}
 * @line{@code{@vdots} @equiv @vdots}
 * @line{@code{@ldots} @equiv @ldots}
 * @line{@code{@subset} @equiv @subset}
 * @line{@code{@subseteq} @equiv @subseteq}
 * @line{@code{@times} @equiv @times}
 * @line{@code{@equiv} @equiv @equiv}
 * @line{@code{@space} @equiv @space}
 * @line{@code{@neg} @equiv @neg}
 * @line{@code{@neq} @equiv @neq}
 * @line{@code{@forall} @equiv @forall}
 * @line{@code{@exists} @equiv @exists}
 * @line{@code{@lambda} @equiv @lambda}
 * @line{@code{@int} @equiv @int}
 * @end[array]
 * $$
 *
 * @end[doc]
 *)
declare math_colon
declare math_rightarrow
declare math_Rightarrow
declare math_leftarrow
declare math_Leftarrow
declare math_leftrightarrow
declare math_Leftrightarrow
declare math_longleftrightarrow

declare math_le
declare math_ge
declare math_wedge
declare math_vee
declare math_phi
declare math_varphi
declare math_cap
declare math_cup
declare math_bigcap
declare math_bigcup
declare math_in
declare math_cdot
declare math_cdots
declare math_vdots
declare math_ldots
declare math_subset
declare math_subseteq
declare math_times
declare math_equiv
declare math_space
declare math_neg
declare math_neq
declare math_forall
declare math_exists
declare math_alpha
declare math_beta
declare math_lambda
declare math_epsilon
declare math_Gamma
declare math_vdash
declare math_int
declare math_lbrace
declare math_rbrace
declare math_quad
declare math_qquad
declare math_bullet
declare math_left[s]
declare math_right[s]

declare math_vec{'e}
declare math_underbrace{'e}
declare math_underbrace{'e1; 'e2}
(*! @docoff *)

dform math_Type_df1 : math_Type =
   math_tt["Type"]

dform math_colon_df1 : mode[tex] :: math_colon =
   izone `"\\colon " ezone

dform math_colon_df2 : except_mode[tex] :: math_colon =
   `":"

dform math_vee_df1 : mode[tex] :: math_vee =
   izone `"\\vee " ezone

dform math_vee_df2 : except_mode[tex] :: math_vee =
   Nuprl_font!vee

dform math_phi_df1 : mode[tex] :: math_phi =
   izone `"\\phi " ezone

dform math_phi_df2 : except_mode[tex] :: math_phi =
   Nuprl_font!phi

dform math_varphi_df1 : mode[tex] :: math_varphi =
   izone `"\\varphi " ezone

dform math_varphi_df2 : except_mode[tex] :: math_varphi =
   Nuprl_font!phi

dform math_wedge_df1 : mode[tex] :: math_wedge =
   izone `"\\wedge " ezone

dform math_wedge_df2 : except_mode[tex] :: math_wedge =
   Nuprl_font!wedge

dform math_rightarrow_df1 : mode[tex] :: math_rightarrow =
   izone `"\\rightarrow " ezone

dform math_rightarrow_df2 : except_mode[tex] :: math_rightarrow =
   Nuprl_font!rightarrow

dform math_Rightarrow_df1 : mode[tex] :: math_Rightarrow =
   izone `"\\Rightarrow " ezone

dform math_Rightarrow_df2 : except_mode[tex] :: math_Rightarrow =
   Nuprl_font!Rightarrow

dform math_leftarrow_df1 : mode[tex] :: math_leftarrow =
   izone `"\\leftarrow " ezone

dform math_leftarrow_df2 : except_mode[tex] :: math_leftarrow =
   Nuprl_font!leftarrow

dform math_Leftarrow_df1 : mode[tex] :: math_Leftarrow =
   izone `"\\Leftarrow " ezone

dform math_Leftarrow_df2 : except_mode[tex] :: math_Leftarrow =
   Nuprl_font!Leftarrow

dform math_leftrightarrow_df1 : mode[tex] :: math_leftrightarrow =
   izone `"\\leftrightarrow " ezone

dform math_leftrightarrow_df2 : except_mode[tex] :: math_leftrightarrow =
   Nuprl_font!shortleftrightarrow

dform math_Leftrightarrow_df1 : mode[tex] :: math_Leftrightarrow =
   izone `"\\Leftrightarrow " ezone

dform math_Leftrightarrow_df2 : except_mode[tex] :: math_Leftrightarrow =
   Nuprl_font!Leftrightarrow

dform math_longleftrightarrow_df1 : mode[tex] :: math_longleftrightarrow =
   izone `"\\longleftrightarrow " ezone

dform math_longleftrightarrow_df2 : except_mode[tex] :: math_longleftrightarrow =
   Nuprl_font!longleftrightarrow

dform math_cap_df1 : mode[tex] :: math_cap =
   izone `"\\cap " ezone

dform math_cap_df2 : except_mode[tex] :: math_cap =
   Nuprl_font!cap

dform math_cup_df1 : mode[tex] :: math_cup =
   izone `"\\cup " ezone

dform math_cup_df2 : except_mode[tex] :: math_cup =
   Nuprl_font!cup

dform math_bigcap_df1 : mode[tex] :: math_bigcap =
   izone `"\\bigcap " ezone

dform math_bigcap_df2 : except_mode[tex] :: math_bigcap =
   Nuprl_font!cap

dform math_bigcup_df1 : mode[tex] :: math_bigcup =
   izone `"\\bigcup " ezone

dform math_bigcup_df2 : except_mode[tex] :: math_bigcup =
   Nuprl_font!cup

dform math_in_df1 : mode[tex] :: math_in =
   izone `"\\in " ezone

dform math_in_df2 : except_mode[tex] :: math_in =
   Nuprl_font!member

dform math_le_df1 : mode[tex] :: math_le =
   izone `"\\le " ezone

dform math_in_df2 : except_mode[tex] :: math_le =
   Nuprl_font!le

dform math_ge_df1 : mode[tex] :: math_ge =
   izone `"\\ge " ezone

dform math_in_df2 : except_mode[tex] :: math_ge =
   Nuprl_font!ge

dform math_cdot_df1 : mode[tex] :: math_cdot =
   izone `"\\cdot " ezone

dform math_cdot_df2 : except_mode[tex] :: math_cdot =
   Nuprl_font!cdot

dform math_cdots_df1 : mode[tex] :: math_cdots =
   izone `"\\cdots " ezone

dform math_cdots_df2 : except_mode[tex] :: math_cdots =
   `"..."

dform math_vdots_df1 : mode[tex] :: math_vdots =
   izone `"\\vdots " ezone

dform math_vdots_df2 : except_mode[tex] :: math_vdots =
   `"..."

dform math_ldots_df1 : mode[tex] :: math_ldots =
   izone `"\\ldots " ezone

dform math_ldots_df2 : except_mode[tex] :: math_ldots =
   `"..."

dform math_subset_df1 : mode[tex] :: math_subset =
   izone `"\\subset " ezone

dform math_subset_df2 : except_mode[tex] :: math_subset =
   Nuprl_font!"subset"

dform math_subseteq_df1 : mode[tex] :: math_subseteq =
   izone `"\\subseteq " ezone

dform math_subseteq_df2 : except_mode[tex] :: math_subseteq =
   Nuprl_font!subseteq

dform math_times_df1 : mode[tex] :: math_times =
   izone `"\\times " ezone

dform math_times_df2 : except_mode[tex] :: math_times =
   Nuprl_font!times

dform math_equiv_df1 : mode[tex] :: math_equiv =
   izone `"\\equiv " ezone

dform math_equiv_df2 : except_mode[tex] :: math_equiv =
   Nuprl_font!equiv

dform math_space_df1 : mode[tex] :: math_space =
   izone `"\\ " ezone

dform math_space_df2 : except_mode[tex] :: math_space =
   " "

dform math_lbrace_df1 : mode[tex] :: math_lbrace =
   izone `"\\{" ezone

dform math_lbrace_df2 : except_mode[tex] :: math_lbrace =
   "{"

dform math_rbrace_df1 : mode[tex] :: math_rbrace =
   izone `"\\}" ezone

dform math_rbrace_df2 : except_mode[tex] :: math_rbrace =
   "}"

dform math_left_df1 : mode[tex] :: math_left[s:s] =
   izone `"\\left" slot[s:s] `" " ezone

dform math_left_df2 : except_mode[tex] :: math_left[s:s] =
   slot[s:s]

dform math_right_df1 : mode[tex] :: math_right[s:s] =
   izone `"\\right" slot[s:s] `" " ezone

dform math_right_df2 : except_mode[tex] :: math_right[s:s] =
   slot[s:s]

dform math_quad_df1 : mode[tex] :: math_quad =
   izone `"\\quad " ezone

dform math_quad_df2 : except_mode[tex] :: math_quad =
   izone `"    " ezone

dform math_qquad_df1 : mode[tex] :: math_qquad =
   izone `"\\qquad " ezone

dform math_qquad_df2 : except_mode[tex] :: math_qquad =
   izone `"      " ezone

dform math_bullet_df1 : mode[tex] :: math_bullet =
   izone `"\\bullet " ezone

dform math_bullet_df2 : except_mode[tex] :: math_bullet =
   izone `"      " ezone

dform math_neg_df1 : mode[tex] :: math_neg =
   izone `"\\neg " ezone

dform math_neg_df2 : except_mode[tex] :: math_neg =
   Nuprl_font!tneg

dform math_neq_df1 : mode[tex] :: math_neq =
   izone `"\\neq " ezone

dform math_neq_df2 : except_mode[tex] :: math_neq =
   Nuprl_font!neq

dform math_forall_df1 : mode[tex] :: math_forall =
   izone `"\\forall " ezone

dform math_forall_df2 : except_mode[tex] :: math_forall =
   Nuprl_font!"forall"

dform math_exists_df1 : mode[tex] :: math_exists =
   izone `"\\exists " ezone

dform math_exists_df2 : except_mode[tex] :: math_exists =
   Nuprl_font!"exists"

dform math_alpha_df1 : mode[tex] :: math_alpha =
   izone `"\\alpha " ezone

dform math_alpha_df2 : except_mode[tex] :: math_alpha =
   Nuprl_font!alpha

dform math_beta_df1 : mode[tex] :: math_beta =
   izone `"\\beta " ezone

dform math_beta_df2 : except_mode[tex] :: math_beta =
   Nuprl_font!beta

dform math_Gamma_df1 : mode[tex] :: math_Gamma =
   izone `"\\Gamma " ezone

dform math_Gamma_df2 : except_mode[tex] :: math_Gamma =
   Nuprl_font!gamma

dform math_vdash_df1 : mode[tex] :: math_vdash =
   izone `"\\vdash " ezone

dform math_vdash_df2 : except_mode[tex] :: math_vdash =
   Nuprl_font!vdash

dform math_epsilon_df1 : mode[tex] :: math_epsilon =
   izone `"\\epsilon " ezone

dform math_epsilon_df2 : except_mode[tex] :: math_epsilon =
   Nuprl_font!epsilon

dform math_lambda_df1 : mode[tex] :: math_lambda =
   izone `"\\lambda " ezone

dform math_lambda_df2 : except_mode[tex] :: math_lambda =
   Nuprl_font!lambda

dform math_int_df1 : mode[tex] :: math_int =
   izone `"{\\mathbb Z}" ezone

dform math_int_df2 : except_mode[tex] :: math_int =
   Nuprl_font!mathbbZ

dform math_vec_df1 : mode[tex] :: math_vec{'e} =
   izone `"\\vec{" ezone 'e izone `"}" ezone

dform math_vec_df2 : except_mode[tex] :: math_vec{'e} =
   `"vector[" 'e `"]"

dform math_underbrace_df1 : mode[tex] :: math_underbrace{'e} =
   izone `"\\underbrace{" ezone 'e izone `"}" ezone

dform math_underbrace_df2 : except_mode[tex] :: math_underbrace{'e} =
   `"underbrace[" 'e `"]"

dform math_underbrace_df3 : mode[tex] :: math_underbrace{'e1; 'e2} =
   izone `"\\underbrace{" ezone 'e1 izone `"}_{" ezone 'e2 izone `"}" ezone

dform math_underbrace_df4 : except_mode[tex] :: math_underbrace{'e1; 'e2} =
   `"underbrace[" 'e1 `"," 'e2 `"]"

(*!
 * @begin[doc]
 * The `_' and `^' characters are @emph{significant} in math mode
 * (they are plain text in normal mode).  The expression @code{s_t}
 * produces the @tt{subscript} term, and the expression @code{s^t}
 * produces the @tt{superscript} term.
 * @end[doc]
 *)
declare math_subscript{'t1; 't2}
declare math_superscript{'t1; 't2}
(*! @docoff *)

dform tex_math_subscript_df1 : mode[tex] :: math_subscript{'t1; 't2} =
   izone `"{" ezone
   slot{'t1}
   izone `"}_{" ezone
   slot{'t2}
   izone `"}" ezone

dform tex_math_superscript_df1 : mode[tex] :: math_superscript{'t1; 't2} =
   izone `"{" ezone
   slot{'t1}
   izone `"}^{" ezone
   slot{'t2}
   izone `"}" ezone

dform normal_math_subscript_df1 : except_mode[tex] :: math_subscript{'t1; 't2} =
   slot{'t1} `"_" slot{'t2}

dform normal_math_superscript_df1 : except_mode[tex] :: math_superscript{'t1; 't2} =
   slot{'t1} `"^" slot{'t2}

(*!
 * @begin[doc]
 * The @tt{array} and tabular forms produce formatted tables.
 * All @emph{rows} in the table are labeled with the @tt{line}
 * term, and all column elements are labeled with the @tt{item}
 * term.  A typical definition looks as follows:
 *
 * @begin[verbatim]
 * @begin[array, rcl]
 * @line{@item{x} @item{y} @item{z}}
 * ...
 * @end[array]
 * @end[verbatim]
 *
 * The @code{@hline} term can be used in place of a @code{@line}
 * term to produce a horizontal rule spanning the width of the
 * table.  The @code{@cr} term represents the line terminator;
 * it is not necessary in normal usage.
 *
 * As usual, the @code{@line} form can have a @tt{block} definition.
 *
 * @begin[verbatim]
 * @begin[array, lcl]
 * @begin[line]
 * @item{x}
 * @item{y}
 * @item{z}
 * @end[line]
 * ...
 * @end[array]
 * @end[verbatim]
 *
 * The @tt{line} and @tt{item} forms are not strictly necessary;
 * arbitrary block definitions are sufficient.
 *
 * @begin[verbatim]
 * @begin[array, rrl]
 * {{x} {y} {z}}
 * ...
 * @end[array]
 * @end[verbatim]
 *
 * However, the use of the @tt{line} and @tt{item} terms
 * is encouraged.
 * @end[doc]
 *)
declare tabular[placement,tags]{'t}
declare tabular[tags]{'t}
declare line{'t}
declare cr
declare hline
declare arraystretch{'e}
declare multicolumn[cols,align]{'t}

declare math_array[placement,tags]{'t}
declare math_tabular[placement,tags]{'t}
declare math_array[tags]{'t}
declare math_tabular[tags]{'t}
declare math_line{'t}
declare math_item{'t}
declare math_cr
declare math_hline
declare math_arraystretch{'e}
declare math_multicolumn[cols,align]{'t}
(*! @docoff *)

(*
 * TeX display.
 *)
declare tex_strip_white{'l1; 'l2; 't}
declare tex_reverse{'l1; 'l2; 't}
declare tex_apply{'t; 'l}

declare tex_array_lines{'l}
declare tex_array_lns
declare tex_array_line{'l}
declare tex_array_ln

dform array_df1 : mode[tex] :: math_array[tags:s]{'t} =
   izone `"\\begin{array}{" slot[tags:s] `"}" ezone
   tex_strip_white{nil; 't; tex_array_lns}
   izone `"\\end{array}" ezone

dform tabular_df1 : mode[tex] :: math_tabular[tags:s]{'t} =
   izone `"\\begin{tabular}{" slot[tags:s] `"}" ezone
   tex_strip_white{nil; 't; tex_array_lns}
   izone `"\\end{tabular}" ezone

dform tabular_df2 : mode[tex] :: tabular[tags:s]{'t} =
   izone `"\\begin{tabular}{" slot[tags:s] `"}" ezone
   tex_strip_white{nil; 't; tex_array_lns}
   izone `"\\end{tabular}" ezone

dform array_place_df1 : mode[tex] :: math_array[placement:s,tags:s]{'t} =
   izone `"\\begin{array}[" slot[placement:s] `"]{" slot[tags:s] `"}" ezone
   tex_strip_white{nil; 't; tex_array_lns}
   izone `"\\end{array}" ezone

dform tabular_place_df1 : mode[tex] :: math_tabular[placement:s,tags:s]{'t} =
   izone `"\\begin{tabular}[" slot[placement:s] `"]{" slot[tags:s] `"}" ezone
   tex_strip_white{nil; 't; tex_array_lns}
   izone `"\\end{tabular}" ezone

dform tabular_place_df2 : mode[tex] :: tabular[placement:s,tags:s]{'t} =
   izone `"\\begin{tabular}[" slot[placement:s] `"]{" slot[tags:s] `"}" ezone
   tex_strip_white{nil; 't; tex_array_lns}
   izone `"\\end{tabular}" ezone

(*
 * Strip the whitespace from the second argument.
 *)
dform tex_strip_white_df1 : tex_strip_white{'l; cons{comment_white; 'tl}; 't} =
   tex_strip_white{'l; 'tl; 't}

dform tex_strip_white_df2 : tex_strip_white{'l; cons{comment_term{'t1}; 'tl}; 't2} =
   tex_strip_white{cons{'t1; 'l}; 'tl; 't2}

dform tex_strip_white_df3 : tex_strip_white{'l; cons{comment_string[text:s]; 'tl}; 't2} =
   tex_strip_white{cons{comment_block{cons{comment_string[text:s]; nil}}; 'l}; 'tl; 't2}

dform tex_strip_white_df4 : tex_strip_white{'l; cons{comment_block{'t}; 'tl}; 't2} =
   tex_strip_white{cons{comment_block{'t}; 'l}; 'tl; 't2}

dform tex_strip_white_df3 : tex_strip_white{'l; nil; 't} =
   tex_reverse{nil; 'l; 't}

dform tex_reverse_df1 : tex_reverse{'l; cons{'t1; 'tl}; 't2} =
   tex_reverse{cons{'t1; 'l}; 'tl; 't2}

dform tex_reverse_df2 : tex_reverse{'l; nil; 't} =
   tex_apply{'t; 'l}

(*
 * Array lines.
 *)
dform tex_apply_array_lines_df1 : tex_apply{tex_array_lns; 'l} =
   tex_array_lines{'l}

dform tex_array_lines_nil_df1 : tex_array_lines{cons{line{'l}; nil}} =
   tex_strip_white{nil; 'l; tex_array_ln}

dform tex_array_lines_nil_df2 : tex_array_lines{cons{math_line{'l}; nil}} =
   tex_strip_white{nil; 'l; tex_array_ln}

dform tex_array_lines_nil_df3 : tex_array_lines{cons{comment_block{'l}; nil}} =
   tex_strip_white{nil; 'l; tex_array_ln}

dform tex_array_lines_nil_df4 : tex_array_lines{cons{hline; nil}} =
   hline

dform tex_array_lines_nil_df5 : tex_array_lines{cons{math_hline; nil}} =
   math_hline

dform tex_array_lines_cons_df1 : tex_array_lines{cons{line{'l}; cons{'h; 't}}} =
   tex_strip_white{nil; 'l; tex_array_ln}
   izone `"\\\\" ezone
   tex_array_lines{cons{'h; 't}}

dform tex_array_lines_cons_df2 : tex_array_lines{cons{math_line{'l}; cons{'h; 't}}} =
   tex_strip_white{nil; 'l; tex_array_ln}
   izone `"\\\\" ezone
   tex_array_lines{cons{'h; 't}}

dform tex_array_lines_cons_df3 : tex_array_lines{cons{comment_block{'l}; cons{'h; 't}}} =
   tex_strip_white{nil; 'l; tex_array_ln}
   izone `"\\\\" ezone
   tex_array_lines{cons{'h; 't}}

dform tex_array_lines_cons_df4 : tex_array_lines{cons{hline; cons{'h; 't}}} =
   hline
   tex_array_lines{cons{'h; 't}}

dform tex_array_lines_cons_df5 : tex_array_lines{cons{math_hline; cons{'h; 't}}} =
   math_hline
   tex_array_lines{cons{'h; 't}}

dform tex_array_lines_df : tex_array_lines{nil} =
   `""

(*
 * Math line.
 *)
dform tex_apply_array_line_df1 : tex_apply{tex_array_ln; 'l} =
   tex_array_line{'l}

dform tex_array_line_df1 : tex_array_line{cons{'h; nil}} =
   'h

dform tex_array_line_df2 : tex_array_line{cons{'h; cons{'hd; 'tl}}} =
   'h
   izone `"&" ezone
   tex_array_line{cons{'hd; 'tl}}

dform tex_array_line_df3 : tex_array_line{nil} =
   `""

(*
 * Multicolumn specification.
 *)
dform multicolumn_df : mode[tex] :: multicolumn[cols:s, align:s]{'e} =
   izone `"\\multicolumn{" ezone
   slot[cols:s]
   izone `"}{" ezone
   slot[align:s]
   izone `"}{" ezone
   slot{'e}
   izone `"}" ezone

dform multicolumn_df2 : except_mode[tex] :: multicolumn[cols:s, align:s]{'e} =
   slot{'e}

dform math_multicolumn_df : math_multicolumn[cols:s, align:s]{'e} =
   multicolumn[cols:s, align:s]{'e}

(*
 * Math item.
 *)
dform math_item_df1 : mode[tex] :: math_item{'t} =
   't

(*
 * Return.
 *)
dform math_cr : mode[tex] :: math_cr =
   izone `"\\\\" ezone

dform math_hline : mode[tex] :: math_hline =
   izone `"\\hline " ezone

dform cr_df : mode[tex] :: cr =
   izone `"\\\\" ezone

dform hline_df : mode[tex] :: hline =
   izone `"\\hline " ezone

dform arraystretch_df1 : mode[tex] :: arraystretch{'e} =
   izone `"\\renewcommand{\\arraystretch}{" ezone
   slot{'e}
   izone `"}" ezone

dform arraystretch_df2 : mode[tex] :: math_arraystretch{'e} =
   arraystretch{'e}

(*
 * Normal display.
 *)
dform normal_math_array_df1 : except_mode[tex] :: math_array[tags:s]{'t} =
   pushm[0] szone
   tex_strip_white{nil; 't; tex_array_lns}
   ezone popm

dform normal_math_tabular_df1 : except_mode[tex] :: math_tabular[tags:s]{'t} =
   pushm[0] szone
   tex_strip_white{nil; 't; tex_array_lns}
   ezone popm

dform normal_math_line_df1 : except_mode[tex] :: line{'l} =
   pushm[3] szone 'l ezone popm

dform normal_math_line_df2 : except_mode[tex] :: math_line{'l} =
   pushm[3] szone 'l ezone popm

dform normal_math_item_df1 : except_mode[tex] :: math_item{'l} =
   hspace 'l

dform normal_math_cr_df1 : except_mode[tex] :: math_cr =
   hspace

dform normal_math_hline_df1 : except_mode[tex] :: math_hline =
   `"===="

dform normal_math_cr_df1 : except_mode[tex] :: cr =
   hspace

dform normal_math_hline_df1 : except_mode[tex] :: hline =
   `"===="

(*!
 * @begin[doc]
 * The following macros define higher-level macros.
 * The @tt{defrule} term is used to format the output as a rule
 * definition.  The @i{name} argument is the name of the rule; the
 * @i{args} term represents the arguments; the @i{hyps} are the subgoals
 * of the rule; and the @i{goal} is the goal.  The @code{@cr} term
 * is allowed in the @i{hyps} and the @i{goal} to produce
 * multi-line definitions.
 *
 * $$
 * @defrule{name; args; hyps; goal}
 * $$
 *
 * The @tt{rulebox} macro represents the contents of a rule box.
 * The @code{@cr} form is allowed in the @i{hyps} and @i{goal}
 * arguments.
 * $$
 * @rulebox{tac; args; hyps; goal}
 * $$
 *
 * The @tt[sequent] term displays a sequent definition.
 * $$
 * @sequent{ext; hyps; goal}
 * $$
 * @end[doc]
 *)
declare math_defrule{'name; 'args; 'hyps; 'goal}
declare math_rulebox{'tac; 'args; 'hyps; 'goal}
declare math_sequent{'ext; 'hyps; 'goal}
(*! @docoff *)

(*
 * TeX display.
 *)
dform tex_math_defrule_df1 : mode[tex] :: math_defrule{'name; 'args; 'hyps; 'goal} =
   izone `"{\\defrule{" ezone
   'name
   izone `"}{" ezone
   'args
   izone `"}{" ezone
   'hyps
   izone `"}{" ezone
   'goal
   izone `"}}" ezone

dform tex_math_rulebox_df1 : mode[tex] :: math_rulebox{'name; 'args; 'hyps; 'goal} =
   izone `"{\\xtac{" ezone
   'name
   izone `"}{" ezone
   'args
   izone `"}{" ezone
   'hyps
   izone `"}{" ezone
   'goal
   izone `"}}" ezone

dform tex_math_sequent_df1 : mode[tex] :: math_sequent{'ext; 'hyps; 'goal} =
   izone `"{\\xsequent{" ezone
   'ext
   izone `"}{" ezone
   'hyps
   izone `"}{" ezone
   'goal
   izone `"}}" ezone

dform normal_math_defrule_df1 : except_mode[tex] :: math_defrule{'name; 'args; 'hyps; 'goal} =
   pushm[3] szone
   keyword["rule"] `" " slot{'name} `" " slot{'args} `"=" hspace
   slot{'hyps} `"-->" hspace
   slot{'goal}
   ezone popm

dform normal_math_rulebox_df1 : except_mode[tex] :: math_rulebox{'name; 'args; 'hyps; 'goal} =
   pushm[3] szone
   slot{'hyps} hspace
   keyword["BY"] `" " slot{'name} `" " slot{'args} hspace
   slot{'goal}
   ezone popm

dform normal_math_sequent_df1 : except_mode[tex] :: math_sequent{'ext; 'hyps; 'goal} =
   pushm[3] szone
   keyword["sequent ["] slot{'ext} keyword["] "]
   slot{'hyps} `" " Nuprl_font!vdash hspace
   slot{'goal}
   ezone popm

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
