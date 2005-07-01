doc <:doc<
   @module[Mfir_auto]

   The @tt[Mfir_auto] module defines the basic constructs needed
   to automate the FIR theory.

   @docoff
   ------------------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.  Additional
   information about the system is available at
   http://www.metaprl.org/

   Copyright (C) 2002 Brian Emre Aydemir, Caltech

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

   Author: Brian Emre Aydemir
   @email{emre@cs.caltech.edu}
   @end[license]
>>

extends Base_theory

open Auto_tactic
open Dtactic


(*
 * fir_auto_prec is intended to be used as the auto_prec for
 * adding FIR theory rules to the autoT tactic.
 *)

let fir_auto_prec = create_auto_prec [trivial_prec; d_prec] []
