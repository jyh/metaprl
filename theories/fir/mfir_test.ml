(*!
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
 * Tactic to try: @tt["repeatT (autoT thenT rwh reduceC 0)"]
 * @end[doc]
 *)

interactive bool1 :
   sequent [mfir] { >- "true" } -->
   sequent [mfir] { >-
      ifthenelse{ "and"{ not{"false"}; "not"{ "or"{ "false"; "true" } } };
         "false"; "true" } }

interactive arith1 :
   sequent [mfir] { >- 42 } -->
   sequent [mfir] { >-  (-(6 /@ -3) +@ 5) *@ (10 -@ 4) }

interactive arith2 :
   sequent [mfir] { >- 2 } -->
   sequent [mfir] { >- int_min{ 2; 3 } }

interactive list1 :
   sequent [mfir] { >- 2 } -->
   sequent [mfir] { >- length{ cons{1; cons{2; nil}} } }

interactive list2 :
   sequent [mfir] { >- 2 } -->
   sequent [mfir] { >- nth_elt{ 2; cons{0; cons{1; cons{2; cons{3; nil}}}} } }

interactive int_set1 :
   sequent [mfir] { >- "false" } -->
   sequent [mfir] { >- member{ 1024;
      intset[32, "signed"]{ cons{ interval{ 0; 3 };
                            cons{ interval{ 5; 8 }; nil } } } } }

interactive int_set2 :
   sequent [mfir] { >- intset[32, "signed"]{ cons{ interval{ 0; 12 }; nil } } } -->
   sequent [mfir] { >- normalize{
      intset[32, "signed"]{ cons{ interval{ 0; 2 };
                            cons{ interval{ 3; 8 };
                            cons{ interval{ 9; 12 }; nil } } } } } }

interactive int_set3 :
   sequent [mfir] { >-
      intset[32, "signed"]{ cons{ interval{ 0; 4 };
                            cons{ interval{ 8; 12 }; nil } } } } -->
   sequent [mfir] { >- normalize{
      intset[32, "signed"]{ cons{ interval{ 0; 3 };
                            cons{ interval{ 4; 4 };
                            cons{ interval{ 8; 10 };
                            cons{ interval{ 11; 12 }; nil } } } } } } }

interactive int_set4 :
   sequent [mfir] { >- "false" } -->
   sequent [mfir] { >- subset{
      intset[32, "signed"]{ cons{ interval{ 0; 3 };
                            cons{ interval{ 5; 8 }; nil } } };
      intset[32, "signed"]{ cons{ interval{. -3; 4 };
                            cons{ interval{ 6; 10 }; nil } } } } }

interactive int_set5 :
   sequent [mfir] { >- "true" } -->
   sequent [mfir] { >- subset{
      intset[32, "signed"]{ cons{ interval{ 0; 3 };
                            cons{ interval{ 8; 8 }; nil } } };
      intset[32, "signed"]{ cons{ interval{. -3; 4 };
                            cons{ interval{ 6; 10 }; nil } } } } }

interactive int_set6 :
   sequent [mfir] { >- "false" } -->
   sequent [mfir] { >- set_eq{
      intset[32, "signed"]{ cons{ interval{ 0; 3 };
                            cons{ interval{ 8; 8 }; nil } } };
      intset[32, "signed"]{ cons{ interval{. -3; 4 };
                            cons{ interval{ 6; 10 }; nil } } } } }

interactive int_set7 :
   sequent [mfir] { >- "false" } -->
   sequent [mfir] { >- set_eq{
      intset[32, "signed"]{ cons{ interval{ 0; 3 };
                            cons{ interval{ 11; 11 }; nil } } };
      intset[32, "signed"]{ cons{ interval{. -3; 4 };
                            cons{ interval{ 6; 10 }; nil } } } } }

interactive int_set8 :
   sequent [mfir] { >-
      intset[32, "signed"]{ cons{ interval{ 0; 15 };
                            cons{ interval{ 35; 60 }; nil } } } } -->
   sequent [mfir] { >- union{
      intset[32, "signed"]{ cons{ interval{ 0; 4 };
                            cons{ interval{ 12; 15 }; nil } } };
      intset[32, "signed"]{ cons{ interval{ 3; 13 };
                            cons{ interval{ 35; 60 }; nil } } } } }

(*!
 * @docoff
 *)
