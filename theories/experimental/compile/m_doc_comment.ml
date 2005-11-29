doc <:doc<
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
extends Base_theory

(*
 * Come convenient terms.
 *)
declare math_curry
declare math_xrec
declare math_xwith
declare math_xlet
declare math_xin
declare math_pipe
declare math_xif
declare math_xthen
declare math_xelse
declare math_xreserve
declare math_xand
declare math_xrewrite[label:s]{'e1; 'e2}
declare math_xrewrite2[label:s]{'e1; 'e2}
declare math_semleft
declare math_semright
declare small{'e}
declare math_small{'e}

(*
 * Main judgment.
 *)
declare math_compilable{'e}

dform math_compilable_df : mode[tex] :: math_compilable{'e} =
   math_bf["compilable("] slot{'e} math_bf[")"]

dform math_curry_df1 : mode[tex] :: math_curry =
   math_mathop{math_bf["C"]}

dform math_curry_df2 : except_mode[tex] :: math_curry =
   math_bf["C"]

dform math_xrec_df1 : mode[tex] :: math_xrec =
   math_mathop{math_bf["rec"]}

dform math_xrec_df2 : except_mode[tex] :: math_xrec =
   math_bf["rec"]

dform math_xwith_df1 : mode[tex] :: math_xwith =
   math_mathrel{math_bf["with"]}

dform math_xwith_df2 : except_mode[tex] :: math_xwith =
   math_bf["with"]

dform math_xlet_df1 : mode[tex] :: math_xlet =
   math_mathop{math_bf["let"]}

dform math_xlet_df2 : except_mode[tex] :: math_xlet =
   math_bf["let "]

dform math_xin_df1 : mode[tex] :: math_xin =
   math_mathrel{math_bf["in"]}

dform math_xin_df2 : except_mode[tex] :: math_xin =
   math_bf[" in "]

dform math_pipe_df1 : mode[tex] :: math_pipe =
   izone `"{|}" ezone

dform math_pipe_df2 : except_mode[tex] :: math_pipe =
   `"|"

dform math_xif_df1 : mode[tex] :: math_xif =
   math_mathop{math_bf["if"]}

dform math_xif_df2 : except_mode[tex] :: math_xif =
   math_bf["if "]

dform math_xthen_df1 : mode[tex] :: math_xthen =
   math_mathrel{math_bf["then"]}

dform math_xthen_df2 : except_mode[tex] :: math_xthen =
   math_bf["then "]

dform math_xelse_df1 : mode[tex] :: math_xelse =
   math_mathrel{math_bf["else"]}

dform math_xelse_df2 : except_mode[tex] :: math_xelse =
   math_bf["else "]

dform math_xreserve_df1 : mode[tex] :: math_xreserve =
   math_mathop{math_bf["reserve"]}

dform math_xreserve_df2 : except_mode[tex] :: math_xreserve =
   math_bf["reserve "]

dform math_xand_df1 : mode[tex] :: math_xand =
   math_mathrel{math_bf["and"]}

dform math_xand_df2 : except_mode[tex] :: math_xand =
   math_bf["and "]

dform xrewref_df : mode[tex] :: xrewref[label:s] =
   izone `"{\\xrewref{" ezone slot[label:s] izone `"}}" ezone

dform math_xrewrite_df : mode[tex] :: math_xrewrite[label:s]{'e1; 'e2} =
   izone `"{\\xrewrite{" ezone
   slot[label:s]
   izone `"}{" ezone
   slot{'e1}
   izone `"}{" ezone
   slot{'e2}
   izone `"}}" ezone

dform math_xrewrite2_df : mode[tex] :: math_xrewrite2[label:s]{'e1; 'e2} =
   izone `"{\\xrewriteII{" ezone
   slot[label:s]
   izone `"}{" ezone
   slot{'e1}
   izone `"}{" ezone
   slot{'e2}
   izone `"}}" ezone

dform math_semleft_df : mode[tex] :: math_semleft =
   izone `"{[\\![}" ezone

dform math_semright_df : mode[tex] :: math_semright =
   izone `"{]\\!]}" ezone

dform small_df : mode[tex] :: small{'e} =
   izone `"{\\footnotesize " ezone 'e izone `"}" ezone

dform math_small_df : mode[tex] :: math_small{'e} =
   izone `"{\\footnotesize " ezone 'e izone `"}" ezone

(*
   -*-
   Local Variables:
   fill-column: 100
   End:
   -*-
*)
