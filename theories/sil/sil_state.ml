(*
 * Operations on the state.
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
 * Labels in the state.
 *)
declare first
declare next{'l}
declare if_eq_label{'e1; 'e2; 'e3; 'e4}

(*
 * State operations.
 *)
declare empty
declare fetch{'s; 'v}
declare store{'s; 'v1; 'v2}
declare alloc{'s1; 'v; s2, l. 'e['s2; 'l]}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

(*
 * Operations on labels.
 *)
prim_rw reduce_if_eq_label1 : if_eq_label{first; first; 'e1; 'e2} <--> 'e1
prim_rw reduce_if_eq_label2 : if_eq_label{next{'l1}; first; 'e1; 'e2} <--> 'e2
prim_rw reduce_if_eq_label3 : if_eq_label{first; next{'l1}; 'e1; 'e2} <--> 'e2
prim_rw reduce_if_eq_label4 : if_eq_label{next{'l1}; next{'l2}; 'e1; 'e2} <--> if_eq_label{'l1; 'l2; 'e1; 'e2}


(*
 * Fetch operation.
 *)
prim_rw reduce_fetch : fetch{store{'s; 'l1; 'v}; 'l2} <--> if_eq_label{'l2; 'l1; 'v; fetch{'s; 'l2}}

let resource reduce += [
   << fetch{store{'s; 'l1; 'v1}; 'l2} >>, reduce_fetch;
   << if_eq_label{first; first; 'e1; 'e2} >>, reduce_if_eq_label1;
   << if_eq_label{next{'l1}; first; 'e1; 'e2} >>, reduce_if_eq_label2;
   << if_eq_label{first; next{'l1}; 'e1; 'e2} >>, reduce_if_eq_label3;
   << if_eq_label{next{'l1}; next{'l2}; 'e1; 'e2} >>, reduce_if_eq_label4
]

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_if_eq_label
prec prec_fetch
prec prec_lookup
prec prec_store
prec prec_alloc
prec prec_fetch < prec_lookup
prec prec_store < prec_fetch
prec prec_if_eq_label < prec_store
prec prec_alloc < prec_if_eq_label

(*
 * Labels and booleans.
 *)
declare next_loop{'xnil : Dform; 'first} : Dform

dform first_df : first =
   next_loop{xnil; first}

dform next_df : next{'l} =
   next_loop{xnil; next{'l}}

dform next_loop_df1 : next_loop{'index; first} =
   `"L" df_length{'index}

dform next_loop_df2 : next_loop{'index; next{'l}} =
   next_loop{xcons{xnil; 'index}; 'l}

dform next_loop_df3 : next_loop{'index; 'l} =
   `"L{" slot{'l} `"+" df_length{'index} `"}"

dform ifthenelse_df : parens :: "prec"[prec_if_eq_label] :: if_eq_label{'e1; 'e2; 'e3; 'e4} =
   szone pushm[0] pushm[3] keyword["if "] szone{'e1} `" =l" hspace slot{'e2} keyword[" then"] hspace
   szone{'e3} popm hspace
   pushm[3] keyword["else"] hspace szone{'e4} popm popm ezone

(*
 * Store operations.
 *)
dform empty_df : empty =
   keyword["[]"]

dform alloc_df : parens :: "prec"[prec_alloc] :: alloc{'s; 'v; s2, l. 't} =
   szone pushm[3] `"let " slot{'s2} `"," slot{'l} `"= alloc(" slot{'s} `"," hspace slot{'v} `") in" hspace slot{'t} popm ezone

dform fetch_df : parens :: "prec"[prec_fetch] :: fetch{'s; 'v} =
   slot{'s} `"." slot{'v}

dform store_df : parens :: "prec"[prec_store] :: store{'s; 'v1; 'v2} =
   szone pushm[3] slot{'s} `"." slot{'v1} " " Nuprl_font!leftarrow hspace slot{'v2} popm ezone

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
