(*
 * This is a model of the state as a function from labels
 * to values.
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

extends Itt_theory
extends Sil_state

open Sil_state

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*
 * Equality on labels as a Boolean value.
 *)
declare eq_label{'l1; 'l2}
declare le_label{'l1; 'l2}

(*
 * Our own versions of the state.
 *)
declare empty
declare fetch{'s; 'v}
declare store{'s; 'v1; 'v2}
declare alloc{'s1; 'v; s2, l. 'e['s2; 'l]}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_eq_label
prec prec_le_label
prec prec_le_label < prec_eq_label

dform eq_label_df : parens :: "prec"[prec_eq_label] :: eq_label{'l1; 'l2} =
   slot{'l1} `"=l " slot{'l2}

dform le_label_df : parens :: "prec"[prec_le_label] :: le_label{'l1; 'l2} =
   slot{'l1} Nuprl_font!le `"l " slot{'l2}

dform empty_df : empty =
   `"{}"

dform fetch_df : parens :: "prec"[prec_fetch] :: fetch{'s; 'v} =
   slot{'s} `"(" slot{'v} `")"

dform store_df : parens :: "prec"[prec_store] :: store{'s; 'v1; 'v2} =
   slot{'s} `"(" slot{'v1} Nuprl_font!leftarrow slot{'v2} `")"

dform alloc_df : parens :: "prec"[prec_alloc] :: alloc{'s; 'v; s2, l. 't} =
   szone pushm[3] `"let# " slot{'s2} `"," slot{'l} `"= alloc(" slot{'s} `"," hspace slot{'v} `") in" hspace slot{'t} popm ezone

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

(*
 * For simplicity, labels are unit lists.
 * It would also be reasonable to use the natural numbers,
 * but that would require more work on arithmetic.
 *)
prim_rw unfold_first : first <--> nil
prim_rw unfold_next : next{'l} <--> cons{it; 'l}

(*
 * Comparsions.
 *)
prim_rw unfold_eq_label : eq_label{'e1; 'e2} <-->
   (list_ind{'e1; lambda{e2. list_ind{'e2; btrue; u, v, g. bfalse}};
                u1, v1, g1. lambda{e2. list_ind{'e2; bfalse; u2, v2, g2. 'g1 'v2}}} 'e2)

prim_rw unfold_if_eq_label : if_eq_label{'e1; 'e2; 'e3; 'e4} <-->
   ifthenelse{eq_label{'e1; 'e2}; 'e3; 'e4}

interactive_rw reduce_eq_label1 : eq_label{first; first} <--> btrue
interactive_rw reduce_eq_label2 : eq_label{next{'l1}; first} <--> bfalse
interactive_rw reduce_eq_label3 : eq_label{first; next{'l1}} <--> bfalse
interactive_rw reduce_eq_label4 : eq_label{next{'l1}; next{'l2}} <--> eq_label{'l1; 'l2}

prim_rw unfold_le_label : le_label{'l1; 'l2} <-->
   (list_ind{'l1; lambda{l2. btrue}; u1, v1, g1.
       lambda{l2. list_ind{'l2; bfalse; u2, v2, g2. 'g1 'v2}}} 'l2)

interactive_rw reduce_le_label1 : le_label{first; 'l} <--> btrue
interactive_rw reduce_le_label2 : le_label{next{'l1}; first} <--> bfalse
interactive_rw reduce_le_label3 : le_label{next{'l1}; next{'l2}} <--> le_label{'l1; 'l2}

let resource reduce += [
   << eq_label{first; first} >>, reduce_eq_label1;
   << eq_label{next{'l1}; first} >>, reduce_eq_label2;
   << eq_label{first; next{'l1}} >>, reduce_eq_label3;
   << eq_label{next{'l1}; next{'l2}} >>, reduce_eq_label4;
   << le_label{first; 'l} >>, reduce_le_label1;
   << le_label{next{'l}; first} >>, reduce_le_label2;
   << le_label{next{'l1}; next{'l2}} >>, reduce_le_label3
]

interactive_rw reduce_if_eq_label1 : if_eq_label{first; first; 'e1; 'e2} <--> 'e1
interactive_rw reduce_if_eq_label2 : if_eq_label{next{'l1}; first; 'e1; 'e2} <--> 'e2
interactive_rw reduce_if_eq_label3 : if_eq_label{first; next{'l1}; 'e1; 'e2} <--> 'e2
interactive_rw reduce_if_eq_label4 : if_eq_label{next{'l1}; next{'l2}; 'e1; 'e2} <--> if_eq_label{'l1; 'l2; 'e1; 'e2}

(*
 * A state has a bound on its domain as the value of the first label.
 *)
prim_rw unfold_empty : empty <--> lambda{v. next{first}}

prim_rw unfold_fetch : fetch{'s; 'l} <--> ('s 'l)

prim_rw unfold_store : store{'s; 'l1; 'v} <-->
   lambda{l. ifthenelse{eq_label{'l; 'l1}; 'v; .'s 'l}}

prim_rw unfold_alloc : alloc{'s1; 'v; s2, l2. 'e['s2; 'l2]} <-->
   (lambda{l2. lambda{l. ifthenelse{eq_label{'l; first}; next{'l2};
                         ifthenelse{eq_label{'l; 'l2}; 'v;
                         .'s1 'l}}}} ('s1 first))

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
