(*!
 * @spelling{autoT reduceC rwh thenT}
 *
 * @begin[doc]
 * @module[Mfir_test]
 *
 * The @tt[Mfir_test] module is used to test the FIR theory.  Its contents
 * may or may not be sensible.
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

extends Mfir_theory

(*!
 * @begin[doc]
 * Tactic to prove the next rule: @tt{rwh reduceC 0 thenT autoT}
 * @end[doc]
 *)

interactive arith1 :
   sequent [mfir] { >- 42 } -->
   sequent [mfir] { >-  (-(6 /@ -3) +@ 5) *@ (10 -@ 4) }

(*!
 * @begin[doc]
 * Temporary tests.
 * @end[doc]
 *)

interactive t1 :
   sequent [mfir] { >- has_type["atom"]{ atomInt{2}; tyInt } }

interactive t2 :
   sequent [mfir] { >- has_type["atom"]{ atomInt{222222222222222222}; tyInt } }

interactive t3 :
   sequent [mfir] { >- has_type["atom"]{ atomInt{. -2}; tyInt } }

(*!
 * @docoff
 *)
