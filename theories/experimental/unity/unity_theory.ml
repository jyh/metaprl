(*
 * Compose all the stages of the UNITY compiler.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003 Adam Granicz, Caltech
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
 * @email{granicz@cs.caltech.edu}
 * @end[license]
 *)
extends Unity_ast
(*
open Unity_util

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent

open Mp_resource
open Refiner.Refiner.Term
open Term_match_table

let resource test =
   table_resource_info identity extract_data

let testTopC_env e =
   get_resource_arg (env_arg e) get_test_resource

let testTopC = funC testTopC_env

let testC =
   repeatC (higherC testTopC)

let testT =
   test_prog
*)
(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
