(*!
 * @begin[doc]
 * @module[Mfir_basic]
 *
 * The @code{Mfir_basic} module declares basic terms needed to
 * support the @MetaPRL representation of the FIR.
 * @end[doc]
 *
 * ------------------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.  Additional
 * information about the system is available at
 * http://www.metaprl.org/
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
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
 * Author: Brian Emre Aydemir
 * @email{emre@cs.caltech.edu}
 * @end[license]
 *)

extends Base_theory

(**************************************************************************
 * Declarations.
 **************************************************************************)

(*
 * Integers.
 *)

declare number[i:n]

(*
 * Lists.
 *)

declare nil
declare cons{ 'elt; 'tail }

(*
 * Integer sets.
 *)

declare interval[left:n, right:n]
declare intset{ 'interval_list }
declare rawintset[precision:n, sign:s]{ 'interval_list }
