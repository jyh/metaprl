(*
 * This is the definition of a Simple Imperative Language.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1999 Jason Hickey, Cornell University
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
 * jyh@cs.cornell.edu
 *)

extends Base_theory

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*
 * Numbers.
 *)
declare number[i:n]
declare "add"{'e1; 'e2}
declare "sub"{'e1; 'e2}
declare "if"{'e1; 'e2; 'e3; 'e4}

(*
 * Disjoint union.
 *)
declare inl{'e1}
declare inr{'e1}
declare decide{'e1; x. 'e2['x]; y. 'e3['y]}

(*
 * Tuples.
 *)
declare pair{'e1; 'e2}
declare spread{'e1; x, y. 'e2['x; 'y]}

(*
 * Reference cells.
 *)
declare pointer{'l}
declare ref{'e1}
declare deref{'e1}
declare assign{'e1; 'e2}
declare dot

(*
 * Functions.
 *)
declare lambda{v. 'e1['v]}
declare apply{'e1; 'e2}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_add
prec prec_sub
prec prec_if
prec prec_decide
prec prec_spread
prec prec_apply
prec prec_assign
prec prec_lambda
prec prec_add < prec_apply
prec prec_sub = prec_add
prec prec_lambda < prec_add
prec prec_spread < prec_lambda
prec prec_decide = prec_spread
prec prec_if = prec_spread

(*
 * Numbers.
 *)
dform number_df : number[i:n] =
   `"#" slot[i:n]

dform add_df : parens :: "prec"[prec_add] :: add{'e1; 'e2} =
   slot["le"]{'e1} `" +" hspace slot{'e2}

dform sub_df : parens :: "prec"[prec_sub] :: sub{'e1; 'e2} =
   slot["le"]{'e1} `" -" hspace slot{'e2}

dform if_df : parens :: "prec"["prec_if"] :: "if"{'e1; 'e2; 'e3; 'e4} =
   szone pushm[0] pushm[3] keyword["if "] slot{'e1} keyword[" = "] slot{'e2} keyword[" then"] hspace
   slot{'e3} popm hspace
   pushm[3] keyword["else"] hspace
   slot{'e4} popm popm

(*
 * Disjoint union.
 *)
dform inl_df : inl{'e1} =
   `"inl(" slot{'e1} `")"

dform inr_df : inr{'e1} =
   `"inr(" slot{'e1} `")"

dform decide_df : parens :: "prec"["prec_decide"] :: decide{'e1; x. 'e2; y. 'e3} =
   szone pushm[1] pushm[3] keyword["match "] slot{'e1} keyword[" with"] hspace
      `"inl(" slot{'x} `") ->" hspace slot{'e2} popm hspace
      pushm[2] `"| inr(" slot{'y} `") ->" hspace slot{'e3} popm popm ezone

(*
 * Pairs.
 *)
dform pair_df : pair{'e1; 'e2} =
   `"(" slot{'e1} `"," hspace slot{'e2} `")"

dform spread_df : parens :: "prec"["prec_spread"] :: spread{'e1; x, y. 'e2} =
   szone pushm[3] keyword["match "] slot{'e1} keyword[" with"] hspace
      `"(" slot{'x} `", " slot{'y} `") ->" hspace slot{'e2} popm ezone

(*
 * Reference cells.
 *)
dform pointer_df : pointer{'l} =
   keyword["&"] slot{'l}

dform ref_df : parens :: "prec"["prec_apply"] :: ref{'e1} =
   keyword["ref "] slot{'e1}

dform deref_df : deref{'e1} =
   keyword["!"] slot{'e1}

dform assign_df : parens :: "prec"["prec_assign"] :: assign{'e1; 'e2} =
   pushm[3] slot{'e1} " " Nuprl_font!leftarrow hspace slot{'e2} popm

dform dot_df : dot =
   Nuprl_font!cdot

(*
 * Functions.
 *)
dform lambda_df : parens :: "prec"["prec_lambda"] :: lambda{v. 'e1} =
   Nuprl_font!lambda slot{'v} `"." slot{'e1}

dform apply_df : parens :: "prec"["prec_apply"] :: apply{'e1; 'e2} =
   slot["le"]{'e1} " " slot{'e2}

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
