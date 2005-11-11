doc <:doc<
   @spelling{unrollings}
   @module[Itt_srec]

   The @tt[Itt_obj_base_rewrite] module defines basic operations of @em{object calculas}.
   It does not define types of objects yet.

   @docoff

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998 Jason Hickey, Cornell University

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

   Author: Alexei Kopylov
   @email{kopylov@cs.caltech.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_record
extends Itt_labels

doc docoff

open Basic_tactics

(******************)
(*  Terms         *)
(******************)

doc <:doc<
  @terms
  @modsubsection{Canonical Terms }
>>

define unfold_obj: obj{self. 'record['self]} <--> lambda {self. 'record['self]}

doc <:doc<
  @modsubsection{Non-canonical Terms }
>>

define unfold_empty_obj {| reduce |}: obj{} <--> obj{self.rcrd}

define unfold_apply: apply[m:t]{'obj} <--> field[m:t]{'obj 'obj}

define unfold_update_field:  update[m:t]{'f;'obj} <--> lambda {self. rcrd[m:t]{'f;'obj 'self}}

define unfold_update_method: update[m:t]{self.'f['self];'obj} <--> lambda {self. rcrd[m:t]{'f['self]; 'obj 'self}}

doc <:doc<
  @bf{Alternative definition of field update.}
>>

interactive_rw unfold_update_field2:
   update[m:t]{'f;'obj} <-->
   update[m:t]{self.'f;'obj}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
  @rewrites
>>

interactive_rw apply_reduce {| reduce |}:
   apply[m:t]{obj{self. 'record['self]}} <--> field[m:t]{'record[ obj{self. 'record['self]} ]}

interactive_rw update_f_reduce {| reduce |}:
   update[m:t]{'f;obj{self. 'record['self]}} <--> obj{self.rcrd[m:t]{'f;'record['self]}}

interactive_rw update_m_reduce {| reduce |}:
   update[m:t]{self.'f['self];obj{self. 'record['self]}} <--> obj{self.rcrd[m:t]{'f['self];'record['self]}}

doc docoff

(******************)
(*  Display Forms *)
(******************)

doc docoff
open Itt_dfun

declare obj_dot
dform obj_dot_df : obj_dot = subzero
declare obj_assign
dform obj_assign_df : obj_assign = `":="

dform obj_df  : parens :: except_mode [src] :: "prec"[prec_lambda] ::
      obj{self.'a} = `"obj " slot{'self} `"." slot{'a}

dform obj_empty_df  : parens :: except_mode [src] :: "prec"[prec_lambda] ::
      obj{} = `"obj " rcrd

dform apply_df  : parens :: except_mode [src] ::
      apply[m:t]{'o} = slot{'o} obj_dot label[m:t]

dform update_field_df  : parens :: except_mode [src] ::
      update[m:t]{'f;'o} = slot{'o} obj_dot label[m:t] obj_assign slot{'f}

dform update_method_df  : parens :: except_mode [src] ::
      update[m:t]{s.'f;'o} = slot{'o} obj_dot label[m:t] "(" slot{'s} ")" obj_assign slot{'f}


(******************)
(*  Examples      *)
(******************)

doc <:doc<
  @modsection{Examples}
  @modsubsection{Basic Examples}
>>



define flea : flea <-->
   obj{ self.
           {x=1;
            getX = apply["x":t]{'self};                            (* x *)
            getNextX =  apply["x":t]{'self} +@ 1;                  (* x+1 *)
            move = update["x":t]{apply["getNextX":t]{'self};'self} (* x:=getNextX *)
           }}

interactive_rw example1 : apply["getX":t]{apply["move":t]{apply["move":t]{flea}}} <--> 3

define fastFlea: fastFlea <--> update["getNextX":t]{self. apply["x":t]{'self} +@ 2; flea}
  (* fastFlea = flea . getX := sigma (x+2) *)

interactive_rw example2 : apply["getX":t]{apply["move":t]{apply["move":t]{fastFlea}}} <--> 5


(******************)
(*  Recursion     *)
(******************)
doc <:doc<
  @modsubsection{Recursion}
>>

define recursiveFlea:  recursiveFlea <-->
   update["moveBy":t]{self.
       lambda{n.
         if 'n=@ 0 then 'self
           else apply["moveBy":t]{apply["move":t]{'self}} ('n -@ 1) };
   flea}

interactive_rw example3 : apply["getX":t]{apply["moveBy":t]{recursiveFlea} 5} <--> 6

doc <:doc<
  @modsubsection{Mutual Recursion}
>>

define feeFoo: feeFoo <-->
   obj{ self.
           {foo =  lambda{n. ifthenelse{ 'n =@ 0 ;
                                         0 ;
                                         .apply["fee":t]{'self} ('n -@ 1)}};
            fee =  lambda{n. ifthenelse{ 'n =@ 0 ;
                                         1 ;
                                         .apply["foo":t]{'self} ('n -@ 1)}}
           }}


interactive_rw example4 : (apply["foo":t]{feeFoo} 5) <--> 1

