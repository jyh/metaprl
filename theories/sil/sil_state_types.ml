(*
 * Possible types of the state.
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
 * Type of labels into the state.
 *)
declare label_type

(*
 * Declaration lists.
 *)
declare empty_decl
declare store_decl{'D; 'l; 'T}
declare alloc_decl{'D; 'T}

(*
 * State from a declaration.
 *)
declare state{'D}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

declare decl_df{'D}
declare decl_inner{'D}

dform label_type_df : label_type =
   `"#Label"

dform empty_decl_df : empty_decl =
   decl_df{empty_decl}

dform store_decl_df : store_decl{'D; 'l; 'T} =
   decl_df{store_decl{'D; 'l; 'T}}

dform alloc_decl_df : alloc_decl{'D; 'T} =
   decl_df{alloc_decl{'D; 'T}}

dform decl_df_df : decl_df{'D} =
   szone pushm[1] `"{" decl_inner{'D} `"}" popm ezone

dform decl_inner_df1 : decl_inner{empty_decl} =
   Nuprl_font!cdot

dform decl_inner_df2 : decl_inner{store_decl{'D; 'l; 'T}} =
   decl_inner{'D} `";" hspace slot{'l} `":" slot{'T}

dform decl_inner_df3 : decl_inner{alloc_decl{'D; 'T}} =
   decl_inner{'D} `";" hspace `"ref " slot{'T}

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
