(*
 * Simple Imperative Types.
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

include Base_theory

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare unit
declare int
declare union{'A; 'B}
declare prod{'A; v. 'B['v]}
declare "fun"{'A; v. 'B['v]}
declare ref_type

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_union
prec prec_prod
prec prec_fun
prec prec_union < prec_fun
prec prec_fun < prec_prod

dform unit_df : unit =
   `"#Unit"

dform int_df : int =
   `"#" Nuprl_font!mathbbZ

(*
 * Unions.
 *)
declare union_df{'a}

dform union_df1 : parens :: "prec"[prec_union] :: union{'A; 'B} =
   szone pushm[0] slot["le"]{'A} union_df{'B} popm ezone

dform union_df2 : union_df{union{'A; 'B}} =
   hspace `"|# " slot["le"]{'A} union_df{'B}

dform union_df3 : union_df{'A} =
   hspace `"|# " " " slot{'A}

(*
 * Products.
 *)
declare prod_df{'a}

dform prod_df1 : parens :: "prec"[prec_prod] :: prod{'A; v. 'B} =
   szone pushm[0] slot{'v} `":" slot["le"]{'A} prod_df{'B} popm ezone

dform prod_df2 : prod_df{prod{'A; v. 'B}} =
   hspace Nuprl_font!times `"# " slot{'v} `":" slot["le"]{'A} prod_df{'B}

dform prod_df3 : prod_df{'A} =
   hspace Nuprl_font!times `"# " slot{'A}

(*
 * Functions.
 *)
declare fun_df{'a}

dform fun_df1 : parens :: "prec"[prec_fun] :: "fun"{'A; v. 'B} =
   szone pushm[0] slot{'v} `":" slot["le"]{'A} fun_df{'B} popm ezone

dform fun_df2 : fun_df{."fun"{'A; v. 'B}} =
   hspace Nuprl_font!rightarrow `"# " slot{'v} `":" slot["le"]{'A} fun_df{'B}

dform fun_df3 : fun_df{'A} =
   hspace Nuprl_font!rightarrow `"# " slot{'A}

(*
 * Reference cells.
 *)
dform ref_df : ref_type =
   `"ref"

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
