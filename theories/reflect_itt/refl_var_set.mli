(*
 * Set of variables.
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
 * Copyright (C) 1998 Jason Hickey, Cornell University
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

include Refl_var

open Tactic_type.Tacticals
open Tactic_type.Conversionals

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare var_set
declare vequal

declare vempty
declare vmember{'v; 's}
declare vunion{'s1; 's2}
declare vsub{'s1; 's2}
declare vsingleton{'v}
declare voflist{'sl}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

topval unfold_vempty : conv
topval unfold_vequal : conv
topval unfold_var_set : conv
topval unfold_vmember : conv
topval unfold_vunion : conv
topval unfold_visect : conv
topval unfold_vsub : conv
topval unfold_vsingleton : conv
topval unfold_voflist : conv

topval fold_vempty : conv
topval fold_vequal : conv
topval fold_var_set : conv
topval fold_vmember : conv
topval fold_vunion : conv
topval fold_visect : conv
topval fold_vsub : conv
topval fold_vsingleton : conv
topval fold_voflist : conv

topval vequal_equalpT : tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
