(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Contains test theorems and programs.
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
 * Email:  emre@its.caltech.edu
 *)

include Mc_theory

(*
 * The term to represent I don't know what should go in a spot,
 * but it doesn't really matter anyways.
 *)
declare darb
dform darb_df : except_mode[src] :: darb = `"Darb"

(*
 * Tests.
 *)

interactive test1 'H :
   sequent ['ext] { 'H >- 20 } -->
   sequent ['ext] { 'H >-
      apply{ apply{ fix{ g. lambda{ f.
         ifthenelse{ eq_atom{ 'f; token["who":t] };
            20;
            lambda{ x. ifthenelse{ beq_int{'x;50};
               apply{ 'g; token["who":t] }; it } } } } }; token["splat":t] };
   20 } }

interactive test2 'H :
   sequent ['ext] { 'H >- 20 } -->
   sequent ['ext] { 'H >-
      apply{ apply{ fix{ g. lambda{ f.
         ifthenelse{ eq_atom{ 'f; token["who":t] };
            20;
            lambda{ x. ifthenelse{ beq_int{'x;50};
               apply{ 'g; token["who":t] }; it } } } } }; token["splat":t] };
   50 } }

