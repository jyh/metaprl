(*
 * preFIR term declarations and reductions (conversionals).
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
 * Copyright (C) 2002 Adam Granicz, Caltech
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
 * Author: Adam Granicz
 * Email:  granicz@cs.caltech.edu
 *)

include Base_theory

open Tactic_type.Conversionals

(*
 * Instead of MetaPRL variable[v:v] variables, Phobos
 * generates variable[v:s] with Mp_mc_fir_phobos_exp as the
 * module.  Due to how iforms work, it is necessary to
 * define the reduction here and apply it as the final
 * rewrite in taking a preFIR term to a proper FIR term.
 * (See Mp_mc_fir_phobos.)
 *)

declare variable[v:s]

val reduce_phobos_variable : conv
