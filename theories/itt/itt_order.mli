(*
 * Partial order, linear order, etc.
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
 * Copyright (C) 2003 Yegor Bryukhov, GC CUNY
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
 * Author: Yegor Bryukhov
 * Email : ybryukhov@gc.cuny.edu
 *)

extends Itt_record

open Tactic_type.Conversionals

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

define unfold_relation : relation[i:l, rel:t] <-->
	record[rel:t]{r. 'r^car -> 'r^car -> univ[i:l]; {car: univ[i:l]} }

define unfold_isReflexive : isReflexive[rel:t]{'O} <-->
	all a: 'O^car. field[rel:t]{'O} 'a 'a

define unfold_isAntisym : isAntisym[rel:t]{'O} <-->
	all a: 'O^car. all b: 'O^car. ((field[rel:t]{'O} 'a 'b) & (field[rel:t]{'O} 'b 'a) => ('a='b in 'O^car))

define unfold_isTransitive : isTransitive[rel:t]{'O} <-->
	all a: 'O^car. all b: 'O^car. all c: 'O^car. ((field[rel:t]{'O} 'a 'b) & (field[rel:t]{'O} 'b 'c) => (field[rel:t]{'O} 'a 'c))

define unfold_isPartialOrder1 : isPartialOrder[rel:t]{'O} <-->
	isReflexive[rel:t]{'O} & isTransitive[rel:t]{'O} & isAntisym[rel:t]{'O}

define unfold_partialOrder1 : partialOrder[i:l,rel:t] <-->
   { O: relation[i:l,rel:t] | isPartialOrder[rel:t]{'O} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval unfold_isPartialOrder : conv
topval unfold_partialOrder : conv

topval fold_relation : conv
topval fold_isReflexive : conv
topval fold_isTransitive : conv
topval fold_isAntisym : conv
topval fold_isPartialOrder1 : conv
topval fold_isPartialOrder : conv
topval fold_partialOrder1 : conv
topval fold_partialOrder : conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
