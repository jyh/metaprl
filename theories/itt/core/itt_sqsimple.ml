doc <:doc<
   @module[Itt_sqsimple]

   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2004-2005 MetaPRL Group, California Institute of Technology

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

   Authors:
    Alexei Kopylov @email{kopylov@cs.caltech.edu}
    Aleksey Nogin @email{nogin@cs.caltech.edu}

   @end[license]
>>

doc <:doc<
   @parents
>>

extends Itt_logic
extends Itt_squiggle

open Basic_tactics
open Term_match_table
open Itt_equal
open Itt_struct

doc <:doc<
   @modsection{Definition}
   A type is said to be squiggle simple if only squiggle equal elements are equal in this type.
>>

define unfold_sqsimple: sqsimple{'T} <--> "type"{'T} & all x:'T. all y:'T. ('x='y in 'T => 'x~'y)

doc docoff

let fold_sqsimple = makeFoldC << sqsimple{'T} >> unfold_sqsimple

let sqsimple_term = << sqsimple{'T} >>
let sqsimple_opname = opname_of_term sqsimple_term
let is_sqsimple_term = is_dep0_term sqsimple_opname
let mk_sqsimple_term = mk_dep0_term sqsimple_opname
let dest_sqsimple_term = dest_dep0_term sqsimple_opname

let extract_sqsimple tbl =
   let rec is_sqsimple t =
      try
         List.for_all is_sqsimple (fst (lookup_rmap tbl select_all t))
      with
         Not_found ->
            false
   in
      is_sqsimple

let resource (term * term list, term -> bool) sqsimple =
   Functional {
      fp_empty = empty_map_table;
      fp_add = (fun tbl (t1, t2) -> add_map tbl t1 t2 ());
      fp_retr = extract_sqsimple
   }

let process_assum name (_, _, t) =
   let t = TermMan.explode_sequent t in
      if is_sqsimple_term t.sequent_concl then
         match SeqHyp.to_list t.sequent_hyps with
            [Context _] ->
               Some (dest_sqsimple_term t.sequent_concl)
          | _ ->
               raise (Invalid_argument ("sqsimple resource annotation: " ^ name ^ ": not supported:
sqsimple assumptions should not have extra hypothesis"))
      else
         None

let process_sqsimple_resource_annotation ?labels name contexts args stmt loc _tac =
   if contexts.spec_addrs <> [||] || contexts.spec_ints <> [||] || args <> [] then
      raise (Invalid_argument ((string_of_loc loc) ^ ": sqsimple resource annotation:
" ^ name ^ ": rules with arguments are not supported yet"));
   rule_labels_not_allowed loc labels;
   let assums, goal = unzip_mfunction stmt in
   let t = dest_sqsimple_term (TermMan.concl goal) in
      [t, Lm_list_util.some_map (process_assum name) assums]

doc <:doc<
   @modsection{Basic Rules}
>>

interactive sqsimple_intro {| intro [] |} :
   [wf] sequent { <H> >- 'T Type } -->
   sequent { <H>; x: 'T; y: 'T; 'x = 'y in 'T >- 'x~'y } -->
   sequent { <H> >- sqsimple{'T} }

let resource intro += <<"type"{sqsimple{'T}}>>, wrap_intro typeEquality

interactive sqsimple_elim {| elim[ThinOption thinT] |} 'H:
      sequent{ <H>; sqsimple{'T}; <J> >- 'x = 'y in 'T } -->
      sequent{ <H>; sqsimple{'T}; <J> >- 'x ~ 'y }

interactive sqsimple_elim2 {| nth_hyp |} 'H:
      sequent{ <H>; sqsimple{'T}; <J> >- "type"{'T} }

interactive sqsimple_sq 'T:
      sequent{ <H> >- sqsimple{'T} } -->
      sequent{ <H> >- 'x = 'y in 'T } -->
      sequent{ <H> >- 'x ~ 'y }

interactive sqsimple 'H :
      [aux] sequent{ <H>; u: 'x = 'y in 'T; <J['u]> >- sqsimple{'T} } -->
      sequent{ <H>; u: 'x = 'y in 'T; <J['u]>; 'x ~ 'y >- 'C['u] } -->
      sequent{ <H>; u: 'x = 'y in 'T; <J['u]> >- 'C['u] }

(* TODO: prove that basic types and operators are sqsimple (exept fun, top, //) *)
(* TODO: subset and subtype of sqsimple type is sqsimple. if X subtupe Y and Y is sqsimple => X subset Y *)

interactive sqsimple_unit {| intro []; sqsimple |} :
   sequent { <H> >- sqsimple{unit} }

interactive sqsimple_prod {| intro []; sqsimple |} :
   sequent { <H> >- sqsimple{'A} } -->
   sequent { <H> >- sqsimple{'B} } -->
   sequent { <H> >- sqsimple{'A * 'B} }

interactive sqsimple_union {| intro []; sqsimple |} :
   sequent { <H> >- sqsimple{'A} } -->
   sequent { <H> >- sqsimple{'B} } -->
   sequent { <H> >- sqsimple{'A + 'B} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
