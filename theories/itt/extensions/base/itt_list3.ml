doc <:doc<
   @module[Itt_list3]

   This is another library of list operations.

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2005 Mojave Group, Caltech

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

   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
   @end[license]

   @parents
>>
extends Itt_pairwise
extends Itt_image
extends Itt_list2
extends Itt_nat

doc docoff

open Basic_tactics
open Itt_struct
open Itt_equal

(*
 * Some arithmetic helper rules.
 *)
interactive nat_plus_one_eq_zero_elim {| elim [] |} 'H :
   [wf] sequent { <H>; x: ('j +@ 1 = 0 in nat); <J['x]> >- 'j in nat } -->
   sequent { <H>; x: ('j +@ 1 = 0 in nat); <J['x]> >- 'C['x] }

interactive one_eq_nat_plus_two_elim {| elim [] |} 'H :
   [wf] sequent { <H>; x: (1 = 'j +@ 2 in nat); <J['x]> >- 'j in nat } -->
   sequent { <H>; x: (1 = 'j +@ 2 in nat); <J['x]> >- 'C['x] }

interactive nat_plus_one_eq_nat_plus_one_elim {| elim [] |} 'H :
   [wf] sequent { <H>; x: ('i +@ 1 = 'j +@ 1 in nat); <J['x]> >- 'i in nat } -->
   [wf] sequent { <H>; x: ('i +@ 1 = 'j +@ 1 in nat); <J['x]> >- 'j in nat } -->
   sequent { <H>; x: 'i = 'j in nat; <J['x]> >- 'C['x] } -->
   sequent { <H>; x: ('i +@ 1 = 'j +@ 1 in nat); <J['x]> >- 'C['x] }

interactive nat_plus_one_eq_nat_plus_two_intro {| intro [] |} :
   [wf] sequent { <H> >- 'j in nat } -->
   [wf] sequent { <H> >- 'k in nat } -->
   sequent { <H> >- 'j = 'k +@ 1 in nat } -->
   sequent { <H> >- 'j +@ 1 = 'k +@ 2 in nat }

doc <:doc<
   Define a relaxed form of list type.  The type << Nil >> includes
   just << nil >>.  The type << Cons >> includes all cons-cells
   << cons{'e1; 'e2} >> for any << 'e1 >> and << 'e2 >>.
>>
define unfold_Nil : Nil <-->
   Img{unit; x. nil}

define unfold_Cons : Cons <-->
   Img{top * top; x. spread{'x; u, v. cons{'u; 'v}}}

define unfold_cons_of_list : cons_of_list{'x} <-->
   list_ind{'x; it; y, l, g. list_ind{'l; lambda{x. 'x}; u, v, g. lambda{x. 'x :: 'g 'u}} 'y}

define unfold_ConsN : Cons{'n} <-->
   Img{{ l: list{top} | length{'l} = 'n +@ 1 in nat }; x. cons_of_list{'x}}

doc <:doc<
   These are types.
>>
interactive nil_wf {| intro [] |} :
   sequent { <H> >- Nil Type }

interactive cons_wf {| intro [] |} :
   sequent { <H> >- Cons Type }

interactive cons_n_wf {| intro [] |} :
   [wf] sequent { <H> >- 'n in nat } -->
   sequent { <H> >- Cons{'n} Type }

doc <:doc<
   Introduction and elimination rules.
>>
interactive nil_intro {| intro [] |} :
   sequent { <H> >- nil in Nil }

interactive nil_elim {| elim [ThinOption thinT] |} 'H :
   sequent { <H>; x: Nil; <J[nil]> >- 'C[nil] } -->
   sequent { <H>; x: Nil; <J['x]> >- 'C['x] }

interactive cons_intro {| intro [] |} :
   sequent { <H> >- cons{'e1; 'e2} in Cons }

interactive cons_elim {| elim [] |} 'H :
   sequent { <H>; u: top; v: top; <J[cons{'u; 'v}]> >- 'C[cons{'u; 'v}] } -->
   sequent { <H>; x: Cons; <J['x]> >- 'C['x] }

interactive list_elim 'H :
   [base] sequent { <H>; <J[nil]> >- 'C[nil] } -->
   [step] sequent { <H>; u: top; v: list; <J[cons{'u; 'v}]> >- 'C[cons{'u; 'v}] } -->
   sequent { <H>; x: list; <J['x]> >- 'C['x] }

interactive cons_elim_member 'H :
   sequent { <H>; x: ('y in Cons); <J['x]>; 'y ~ cons{hd{'y}; tl{'y}} >- 'C['x] } -->
   sequent { <H>; x: ('y in Cons); <J['x]> >- 'C['x] }

(************************************************************************
 * Lemmas for flattening.
 *)
interactive cons_of_list_intro {| intro [] |} :
   [wf] sequent { <H> >- 'i in nat } -->
   [wf] sequent { <H> >- 'l in list } -->
   [wf] sequent { <H> >- length{'l} = 'i +@ 1 in nat } -->
   sequent { <H> >- cons_of_list{'l} in Cons{'i} }

doc docoff

define unfold_list_of_cons : list_of_cons{'i; 'x} <-->
   ind{'i; lambda{x. 'x :: nil}; j, g. lambda{x. list_ind{'x; it; u, v, h. 'u :: 'g 'v}}} 'x

interactive_rw cons_of_list_singleton_reduce {| reduce |} :
   cons_of_list{'e::nil}
   <-->
   'e

interactive_rw cons_of_list_cons_reduce {| reduce |} :
   cons_of_list{'e1::'e2::'e3}
   <-->
   'e1 :: cons_of_list{'e2::'e3}

interactive_rw list_of_cons_zero_reduce {| reduce |} :
   list_of_cons{0; 'e}
   <-->
   'e::nil

interactive_rw list_of_cons_succ_reduce {| reduce |} :
   'i in nat -->
   list_of_cons{'i +@ 1; 'e}
   <-->
   list_ind{'e; it; u, v, g. 'u :: list_of_cons{'i; 'v}}

interactive list_of_cons_wf {| intro [] |} :
   [wf] sequent { <H> >- 'i in nat } -->
   [wf] sequent { <H> >- 'x in Cons{'i} } -->
   sequent { <H> >- list_of_cons{'i; 'x} in list }

interactive list_of_cons_length {| intro [] |} :
   [wf] sequent { <H> >- 'i in nat } -->
   [wf] sequent { <H> >- 'x in Cons{'i} } -->
   sequent { <H> >- length{list_of_cons{'i; 'x}} = 'i +@ 1 in nat }

interactive list_of_cons_is_cons {| intro [] |} :
   [wf] sequent { <H> >- 'n in nat } -->
   [wf] sequent { <H> >- 'n > 0 } -->
   [wf] sequent { <H> >- 'x in Cons{'n} } -->
   sequent { <H> >- list_of_cons{'n; 'x} in Cons }

interactive cons_n_intro_nil {| intro [] |} :
   sequent { <H> >- 'e in Cons{0} }

interactive cons_n_elim_expand 'H :
   [wf] sequent { <H>; x: Cons{'n}; <J['x]> >- 'n in nat } -->
   [wf] sequent { <H>; x: Cons{'n}; <J['x]> >- 'n > 0 } -->
   sequent { <H>; x: Cons{'n}; <J['x]>; 'x ~ cons_of_list{list_of_cons{'n; 'x}} >- 'C['x] } -->
   sequent { <H>; x: Cons{'n}; <J['x]> >- 'C['x] }

interactive cons_n_elim {| elim [] |} 'H :
   [wf] sequent { <H>; x: Cons{'n}; <J['x]> >- 'n in nat } -->
   [wf] sequent { <H>; x: Cons{'n}; <J['x]> >- 'n > 0 } -->
   sequent { <H>; u: top; v: Cons{'n -@ 1}; <J[cons{'u; 'v}]> >- 'C[cons{'u; 'v}] } -->
   sequent { <H>; x: Cons{'n}; <J['x]> >- 'C['x] }

interactive cons_n_intro_cons {| intro [] |} :
   [wf] sequent { <H> >- 'n in nat } -->
   [wf] sequent { <H> >- 'n > 0 } -->
   [wf] sequent { <H> >- 'e2 IN Cons{'n -@ 1} } -->
   sequent { <H> >- cons{'e1; 'e2} in Cons{'n} }

(************************************************************************
 * Squiggle equality.
 *)
define unfold_nth_prefix : nth_prefix{'l; 'i} <-->
   ind{'i; lambda{l. nil}; j, g. lambda{l. list_ind{'l; it; u, v, h. 'u :: 'g 'v}}} 'l

define unfold_nth_suffix : nth_suffix{'l; 'i} <-->
   ind{'i; lambda{l. 'l}; j, g. lambda{l. list_ind{'l; it; u, v, h. 'g 'v}}} 'l

interactive_rw reduce_nth_prefix_zero {| reduce |} :
   nth_prefix{'l; 0}
   <-->
   nil

interactive_rw reduce_nth_suffix_zero {| reduce |} :
   nth_suffix{'l; 0}
   <-->
   'l

interactive_rw reduce_nth_prefix_cons {| reduce |} :
   'i in nat -->
   nth_prefix{'u::'v; 'i +@ 1}
   <-->
   'u :: nth_prefix{'v; 'i}

interactive_rw reduce_nth_suffix_cons {| reduce |} :
   'i in nat -->
   nth_suffix{'u::'v; 'i +@ 1}
   <-->
   nth_suffix{'v; 'i}

interactive split_list 'i 'n :
   [wf] sequent { <H> >- 'n in nat } -->
   [wf] sequent { <H> >- 'l in Cons{'n} } -->
   [wf] sequent { <H> >- 'i in nat } -->
   [wf] sequent { <H> >- 'i < 'n } -->
   sequent { <H> >- 'l ~ append{nth_prefix{'l; 'i}; nth_suffix{'l; 'i}} }

interactive split_list_pair 'i 'n :
   [wf] sequent { <H> >- 'n in nat } -->
   [wf] sequent { <H> >- 'l1 in Cons{'n} } -->
   [wf] sequent { <H> >- 'l2 in Cons{'n} } -->
   [wf] sequent { <H> >- 'i in nat } -->
   [wf] sequent { <H> >- 'i < 'n } -->
   sequent { <H> >- append{nth_prefix{'l1; 'i}; nth_suffix{'l1; 'i}} ~ append{nth_prefix{'l2; 'i}; nth_suffix{'l2; 'i}} } -->
   sequent { <H> >- 'l1 ~ 'l2 }

(************************************************************************
 * Tactics.
 *)
let cons_type_term = << Cons >>

(*
 * Given an expression in Cons, add the split equation.
 *)
let splitConsT t =
   let t_mem = mk_equal_term cons_type_term t t in
      assertT t_mem
      thenLT [idT; cons_elim_member (-1) thenT thinT (-2)]

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
