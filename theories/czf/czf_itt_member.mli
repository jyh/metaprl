(*
 * Membership over the extensional equality.
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

extends Czf_itt_eq

open Refiner.Refiner.Term

open Tactic_type.Tacticals
open Tactic_type.Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare mem{'x; 'y}
declare member{'x; 'y}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

rewrite unfold_mem : mem{'x; 'y} <-->
   set_ind{'y; T, f, g. exst t: 'T. eq{'x; .'f 't}}

rewrite reduce_mem : mem{'x; collect{'T; y. 'f['y]}} <-->
   (exst t: 'T. eq{'x; .'f['t]})

rewrite unfold_member : member{'x; 'y} <-->
   ((isset{'x} & isset{'y}) & mem{'x; 'y})

rewrite reduce_member : member{'x; collect{'T; y. 'f['y]}} <-->
   ((isset{'x} & isset{collect{'T; y. 'f['y]}}) & (exst t: 'T. eq{'x; .'f['t]}))

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * member{'x; 'y} => isset{'x}
 *)
topval memSubstLeftT : term -> tactic
topval memSubstRightT : term -> tactic
topval memberOfT : term -> tactic

(*
 * member{'x; 'y} => isset{'y}
 *)
topval setOfT : term -> tactic

(*
 * Apply seq extensionality.
 *)
topval setExtT : tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
