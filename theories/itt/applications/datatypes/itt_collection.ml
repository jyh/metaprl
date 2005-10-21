doc <:doc<
   @module[Itt_collection]
   The @tt{Itt_collection} module formalized the type of indexed collections.
   See @cite["Nog02a,Nog02b"] for more information.

   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2000-2001
   Alexei Kopylov & Aleksey Nogin, Cornell University

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

   Authors: Alexei Kopylov @email{kopylov@cs.cornell.edu}
            Aleksey Nogin @email{nogin@cs.cornell.edu}

   @end[license]
>>

doc <:doc<
   @parents
>>

extends Itt_bool
extends Itt_subtype
extends Itt_esquash
extends Itt_quotient
extends Itt_logic

doc docoff

open Basic_tactics

open Itt_struct
open Itt_squash
open Itt_tunion
open Itt_int_base

doc <:doc<
   @rules
   @modsubsection{Basic definitions}
>>

(*--- col ---*)

define unfold_col: col[l:l]{'T} <--> ('T -> univ[l:l])

doc docoff
let fold_col = makeFoldC <<col[l:l]{'T}>> unfold_col
doc docon

interactive col_univ {| intro [] |} :
   sequent{ <H> >- 'T in univ[l':l] } -->
   sequent{ <H> >- col[l:l]{'T} in univ[l':l] }

interactive col_wf {| intro [] |} :
   sequent{ <H> >- "type"{'T}} -->
   sequent{ <H> >- "type"{col[l:l]{'T}}}

(*--- col_member ---*)

define unfold_col_member: col_member{'C;'x} <--> esquash{('C 'x)}

doc docoff
let fold_col_member = makeFoldC <<col_member{'C;'x}>> unfold_col_member
doc docon

interactive col_member_univ {| intro [intro_typeinf <<'x>>] |} 'T:
   sequent{ <H> >- 'x in 'T } -->
   sequent{ <H> >- 'C in col[l:l]{'T} } -->
   sequent{ <H> >- col_member{'C;'x} in univ[l:l] }

doc docoff

let univ_typeinf_arg p t =
   let t =
      try get_with_arg p with RefineError _ -> infer_type p t
   in
      [get_univ_arg p; t]

let intro_univ_typeinf t = IntroArgsOption (univ_typeinf_arg, Some t)
let elim_univ_typeinf t = ElimArgsOption (univ_typeinf_arg, Some t)

doc docon

interactive col_member_wf {| intro [intro_univ_typeinf <<'x>>] |} univ[l:l] 'T:
   sequent{ <H> >- 'x in 'T } -->
   sequent{ <H> >- 'C in col[l:l]{'T} } -->
   sequent{ <H> >- "type"{col_member{'C;'x}}}

(*--- col_equal ---*)

define unfold_col_equal: col_equal{'T;'C_1;'C_2} <-->
   (all x:'T. iff{col_member{'C_1;'x};col_member{'C_2;'x}})

interactive col_equal_univ {| intro [] |} :
   sequent{ <H> >- 'T in univ[l:l] } -->
   sequent{ <H> >- 'C_1 in col[l:l]{'T} } -->
   sequent{ <H> >- 'C_2 in col[l:l]{'T} } -->
   sequent{ <H> >- col_equal{'T;'C_1;'C_2} in univ[l:l] }

interactive col_equal_wf {| intro [intro_univ_arg] |} univ[l:l] :
   sequent{ <H> >- "type"{'T}} -->
   sequent{ <H> >- 'C_1 in col[l:l]{'T} } -->
   sequent{ <H> >- 'C_2 in col[l:l]{'T} } -->
   sequent{ <H> >- "type"{ col_equal{'T;'C_1;'C_2} }}

interactive col_equal_reflexivity {| intro [intro_univ_arg] |} univ[l:l] :
   [wf] sequent{ <H> >- "type"{'T}} -->
   [wf] sequent{ <H> >- 'C in col[l:l]{'T} } -->
   sequent{ <H> >-  col_equal{'T;'C;'C} }

interactive col_equal_trans  univ[l:l] 'B:
   [wf] sequent{ <H> >- "type"{'T}} -->
   [wf] sequent{ <H> >- 'A in col[l:l]{'T} } -->
   [wf] sequent{ <H> >- 'C in col[l:l]{'T} } -->
   sequent{ <H> >-  col_equal{'T;'A;'B} }  -->
   sequent{ <H> >-  col_equal{'T;'B;'C} }  -->
   sequent{ <H> >-  col_equal{'T;'A;'C} }

interactive col_equal_sym  univ[l:l] :
   [wf] sequent{ <H> >- "type"{'T}} -->
   [wf] sequent{ <H> >- 'A in col[l:l]{'T} } -->
   [wf] sequent{ <H> >- 'B in col[l:l]{'T} } -->
   sequent{ <H> >-  col_equal{'T;'A;'B} }  -->
   sequent{ <H> >-  col_equal{'T;'B;'A} }

(*--- Col --*)

define unfold_Col :  Col[l:l]{'T} <--> (quot x,y: col[l:l]{'T} // col_equal{'T;'x;'y})

doc docoff
let fold_Col = makeFoldC <<Col[l:l]{'T}>> unfold_Col
doc docon

interactive _Col_wf {| intro [] |} :
   sequent{ <H> >- "type"{'T}} -->
   sequent{ <H> >- "type"{Col[l:l]{'T}}}

interactive _Col_univ {| intro [] |} :
   sequent{ <H> >- 'T in univ[l':l] } -->
   sequent{ <H> >- Col[l:l]{'T} in univ[l':l] }

interactive member_Col {| intro [AutoMustComplete] |} :
  [wf] sequent{ <H> >- "type"{'T}} -->
  sequent{ <H> >- 'C in col[l:l]{'T} } -->
  sequent{ <H> >- 'C in Col[l:l]{'T} }

(*--- col_member ---*)

interactive col_member_univ2 {| intro [intro_typeinf <<'x>>] |} 'T:
   sequent{ <H> >- 'x in 'T } -->
   sequent{ <H> >- 'C in Col[l:l]{'T} } -->
   sequent{ <H> >- col_member{'C;'x} in univ[l:l] }

interactive col_member_wf2 {| intro [intro_univ_typeinf <<'x>>] |} univ[l:l] 'T:
   sequent{ <H> >- 'x in 'T } -->
   sequent{ <H> >- 'C in Col[l:l]{'T} } -->
   sequent{ <H> >- "type"{col_member{'C;'x}}}

interactive col_member_member {| intro []; squash |} :
   sequent{ <H> >- col_member{'C;'x} } -->
   sequent{ <H> >- it in col_member{'C;'x} }

(***===--- connection with types ---===***)

(*--- type_col ---*)

define unfold_type_col : type_col{'T} <--> lambda{x.'x in 'T}

interactive type_col_wf {| intro [] |} :
   sequent{ <H> >- 'T in univ[l:l] } -->
   sequent{ <H> >- type_col{'T} in col[l:l]{'T} }

interactive member_type_col {| intro [] |} :
   sequent{ <H> >- 'x in 'T} -->
   sequent{ <H> >- col_member{type_col{'T};'x}}

(*--- col_type ---*)
define unfold_col_type : col_type{'C;'T} <--> ({ x:'T | col_member{'C;'x} })

interactive col_type_wf {| intro [intro_univ_arg] |} univ[l:l] :
   sequent{ <H> >- "type"{'T}} -->
   sequent{ <H> >- 'C in Col[l:l]{'T} } -->
   sequent{ <H> >- "type"{col_type{'C;'T}}}

doc <:doc< @modsubsection{Basic operations} >>

(*--- singleton ---*)

define unfold_singleton :  singleton{'x; 'T} <--> lambda{y.'x = 'y in 'T}

interactive singleton_wf {| intro [] |} :
   sequent{ <H> >- 'x in 'T } -->
   sequent{ <H> >- 'T in univ[l:l] } -->
   sequent{ <H> >- singleton{'x;'T} in col[l:l]{'T} }

interactive member_singleton {| intro [] |} :
   sequent{ <H> >- 'x = 'y in 'T } -->
   sequent{ <H> >- col_member{singleton{'x; 'T}; 'y}}

interactive member_singleton_elim {| elim [] |} 'H :
   [wf] sequent{ <H>; u:col_member{singleton{'x; 'T}; 'y}; <J['u]> >- 'x in 'T } -->
   [wf] sequent{ <H>; u:col_member{singleton{'x; 'T}; 'y}; <J['u]> >- 'y in 'T } -->
   sequent{ <H>; u:'x = 'y in 'T; <J[it]> >- 'Z[it]} -->
   sequent{ <H>; u:col_member{singleton{'x; 'T}; 'y}; <J['u]> >- 'Z['u] }

(*--- union ---*)

define unfold_union : "union"{'X;x.'Y['x]} <-->
   lambda{t.exst x: 'X. col_member{'Y['x];'t}}

interactive union_wf {| intro [] |} :
   sequent{ <H> >- "type"{'T} } -->
   sequent{ <H> >- 'X in univ[l:l] } -->
   sequent{ <H>; x:'X >- 'Y['x] in Col[l:l]{'T} } -->
   sequent{ <H> >- "union"{'X;x.'Y['x]} in Col[l:l]{'T} }

doc docoff

let univ_with_args_fun p _ = [get_univ_arg p; get_with_arg p]
let intro_univ_with_args = IntroArgsOption (univ_with_args_fun, None)
let elim_univ_with_args = ElimArgsOption (univ_with_args_fun, None)

doc docon

interactive member_union {| intro [intro_univ_with_args] |} univ[l:l] 'z :
   [wf] sequent{ <H>; x:'X >- "type"{col_member{'Y['x];'y}} } -->
   [aux] sequent{ <H> >- 'z in 'X } -->
   sequent{ <H> >- col_member{'Y['z];'y} } -->
   sequent{ <H> >- col_member{"union"{'X;x.'Y['x]};'y} }

interactive member_union_elim {| elim [ThinOption thinT] |} 'H :
   [wf] sequent{ <H>; u:col_member{"union"{'X;x.'Y['x]};'y}; <J> >- "type"{'X} } -->
   [wf] sequent{ <H>; u:col_member{"union"{'X;x.'Y['x]};'y}; <J>; x:'X >- "type"{col_member{'Y['x];'y}} } -->
   sequent{ <H>; u:col_member{"union"{'X;x.'Y['x]};'y}; x:'X; v: col_member{'Y['x];'y}; <J> >- squash{'Z} } -->
   sequent{ <H>; u:col_member{"union"{'X;x.'Y['x]};'y}; <J> >- squash{'Z} }

doc <:doc< @modsubsection{Other operations} >>

(*--- col_filter ---*)

define unfold_col_filter :  col_filter{'C; x.'P['x]} <-->
   lambda{x.col_member{'C;'x} & 'P['x]}

interactive col_filter_wf {| intro [] |} :
   sequent{ <H> >- "type"{'T} } -->
   sequent{ <H>; x:'T >- 'P['x] in univ[l:l] } -->
   sequent{ <H> >- 'C in Col[l:l]{'T} } -->
   sequent{ <H> >- col_filter{'C; x.'P['x]} in Col[l:l]{'T} }

interactive member_col_filter {| intro [intro_univ_arg] |} :
   sequent{ <H> >- col_member{'C;'t}} -->
   sequent{ <H> >- squash{'P['t]}} -->
   sequent{ <H> >- col_member{col_filter{'C; x.'P['x]};'t}}

interactive member_col_filter_elim {| elim [elim_univ_typeinf <<'x>>] |} 'H univ[l:l] 'T :
   [wf] sequent{ <H>; <J> >- 'x in 'T} -->
   [wf] sequent{ <H>; <J>; y:'T >- "type"{'P['y]}} -->
   [wf] sequent{ <H>; <J> >- 'C in Col[l:l]{'T} } -->
   sequent{ <H>; v:col_member{'C;'x}; w:squash{'P['x]}; <J> >- 'Z } -->
   sequent{ <H>; u:col_member{col_filter{'C; y.'P['y]};'x}; <J> >- 'Z }

(*--- isect ---*)

define unfold_isect : "isect"{'S;s.'C['s]} <-->
   lambda{x.all s:'S. col_member{'C['s]; 'x}}

interactive isect_wf {| intro [] |} :
   sequent{ <H> >- "type"{'T}} -->
   sequent{ <H> >- 'S in univ[l:l] } -->
   sequent{ <H>; s:'S >- 'C['s] in Col[l:l]{'T} } -->
   sequent{ <H> >- "isect"{'S;s.'C['s]} in Col[l:l]{'T} }

interactive member_isect {| intro [intro_univ_arg] |} :
   [wf] sequent{ <H> >- "type"{'S} } -->
   sequent{ <H>; s:'S >-  col_member{'C['s];'x}} -->
   sequent{ <H> >- col_member{"isect"{'S;s.'C['s]};'x}}

interactive member_isect_elim {| elim [elim_univ_with_args; ThinOption thinT] |} 'H univ[l:l] 's :
   [wf] sequent{ <H>; u:col_member{"isect"{'S;y.'C['y]};'x}; <J>; y: 'S >- "type"{col_member{'C['y];'x}} } -->
   [aux] sequent{ <H>; u:col_member{"isect"{'S;y.'C['y]};'x}; <J> >- 's in 'S } -->
   sequent{ <H>; u:col_member{"isect"{'S;y.'C['y]};'x}; w:col_member{'C['s];'x}; <J> >- 'Z } -->
   sequent{ <H>; u:col_member{"isect"{'S;y.'C['y]};'x}; <J> >- 'Z }

(*--- none ---*)

define unfold_none : none <--> lambda{x."false"}

interactive none_wf {| intro [] |} :
   sequent{ <H> >- "type"{'T}} -->
   sequent{ <H> >- none in col[l:l]{'T} }

interactive member_none_elim {| elim [] |} 'H :
   sequent{ <H>; u:col_member{none; 'y}; <J> >- 'Z}

(*--- add ---*)

define unfold_add : add{'C_1;'C_2} <--> "union"{bool; b. ifthenelse{'b;'C_1;'C_2}}

doc docoff
let fold_add = makeFoldC <<add{'C_1;'C_2}>> unfold_add
doc docon

interactive add_wf {| intro [] |} :
   sequent{ <H> >- "type"{'T}} -->
   sequent{ <H> >- 'C_1 in Col[l:l]{'T} } -->
   sequent{ <H> >- 'C_2 in Col[l:l]{'T} } -->
   sequent{ <H> >- add{'C_1;'C_2} in Col[l:l]{'T} }

interactive member_add1 {| intro [SelectOption 1; intro_univ_typeinf <<'x>>] |}  univ[l:l] 'T :
   [wf] sequent{ <H> >- 'x in 'T } -->
   [wf] sequent{ <H> >- 'C_1 in Col[l:l]{'T} } -->
   [wf] sequent{ <H> >- 'C_2 in Col[l:l]{'T} } -->
   sequent{ <H> >- col_member{'C_1 ; 'x}} -->
   sequent{ <H> >- col_member{add{'C_1;'C_2} ; 'x}}

interactive member_add2 {| intro [SelectOption 2; intro_univ_typeinf <<'x>>] |}  univ[l:l] 'T :
   [wf] sequent{ <H> >- 'x in 'T } -->
   [wf] sequent{ <H> >- 'C_2 in Col[l:l]{'T} } -->
   [wf] sequent{ <H> >- 'C_1 in Col[l:l]{'T} } -->
   sequent{ <H> >- col_member{'C_2 ; 'x}} -->
   sequent{ <H> >- col_member{add{'C_1;'C_2} ; 'x}}

interactive member_add_elim {| elim [elim_univ_typeinf <<'x>>; ThinOption thinT] |} 'H univ[l:l] 'T :
   [wf] sequent{ <H>; u:col_member{add{'C_1;'C_2}; 'x}; <J> >- 'x in 'T } -->
   [wf] sequent{ <H>; u:col_member{add{'C_1;'C_2}; 'x}; <J> >- 'C_1 in Col[l:l]{'T} } -->
   [wf] sequent{ <H>; u:col_member{add{'C_1;'C_2}; 'x}; <J> >- 'C_2 in Col[l:l]{'T} } -->
   sequent{ <H>; u:col_member{add{'C_1;'C_2}; 'x}; v: col_member{'C_1 ; 'x}; <J> >- squash{'Z}} -->
   sequent{ <H>; u:col_member{add{'C_1;'C_2}; 'x}; v: col_member{'C_2 ; 'x}; <J> >- squash{'Z}} -->
   sequent{ <H>; u:col_member{add{'C_1;'C_2}; 'x}; <J> >- squash{'Z}}

(*

(********************** Simplification lemmas **********************)

(* < x:<> | P[x]> = <> in collection(T)  *)
interactive filter_none univ[l:l] :
   sequent{ <H> >- "type"{'T}} -->
   sequent{ <H>; x:'T >- 'P['x] in univ[l:l] } -->
   sequent { <H> >- col_equal{'T;col_filter{none;x.'P['x]};none}}

(*  < x:(if b then C else D) | P[x]> =
 *  (if b then < x:C | P[x]> else < x:D | P[x]>) in collection(T)
 *)
interactive filter_if univ[l:l] :
   sequent{ <H> >- "type"{'T}} -->
   sequent{ <H>; x:'T >- 'P['x] in univ[l:l] } -->
   sequent{ <H> >- 'C in col[l:l]{'T} } -->
   sequent{ <H> >- 'D in col[l:l]{'T} } -->
   sequent{ <H> >- 'b in bool } -->
   sequent { <H> >- col_equal{'T; col_filter{ifthenelse{'b;'C;'D}; x.'P['x]};
                                       ifthenelse{'b; col_filter{'C;x.'P['x]}; col_filter{'D;x.'P['x]}} }}

(*   < x:(c + d) | P[x]> =
 *   (< x:c | P[x]> + < x:d | P[x]>) in collection(T)
 *)
interactive filter_add univ[l:l] :
   sequent{ <H> >- "type"{'T}} -->
   sequent{ <H>; x:'T >- 'P['x] in univ[l:l] } -->
   sequent{ <H> >- 'c in col[l:l]{'T} } -->
   sequent{ <H> >- 'd in col[l:l]{'T} } -->
   sequent { <H> >- col_equal{'T; col_filter{add{'c;'d}; x.'P['x]};
                                       add{ col_filter{'c;x.'P['x]}; col_filter{'d;x.'P['x]}} }}

(*   < x:(×s:S.c[s]) | P[x]> =
 *   ×s:S.< x:c[s] | P[x]> in collection(T)
 *)
interactive filter_union univ[l:l] :
   sequent{ <H> >- "type"{'T}} -->
   sequent{ <H> >- 'S in univ[l:l] } -->
   sequent{ <H>; x:'T >- 'P['x] in univ[l:l] } -->
   sequent{ <H>; s:'S >- 'c['s] in col[l:l]{'T} } -->
   sequent { <H> >- col_equal{'T; col_filter{"union"{'S;s.'c['s]}; x.'P['x]};
                                       "union"{'S; s.col_filter{'c['s];x.'P['x]}} }}

(*   ×s:S.(c[s] + d[s]) =
 *    ((×s:S.c[s]) + (×s:S.d[s])) in collection(T)
 *)
interactive union_add  univ[l:l] :
   sequent{ <H> >- "type"{'T}} -->
   sequent{ <H> >- 'S in univ[l:l] } -->
   sequent{ <H>; s:'S >- 'c['s] in col[l:l]{'T} } -->
   sequent{ <H>; s:'S >- 'd['s] in col[l:l]{'T} } -->
   sequent { <H> >- col_equal{'T; "union"{'S; s.add{'c['s];'d['s]}};
                                       add{ "union"{'S; s.'c['s]}; "union"{'S; s.'d['s]}}  }}

(*     ×s:S.c = c in collection(T)
 *)
interactive union_const  univ[l:l] :
   sequent{ <H> >- "type"{'T}} -->
   sequent{ <H> >- 'S in univ[l:l] } -->
   sequent{ <H> >- 'c in col[l:l]{'T} } -->
   sequent{ <H> >- 'S} -->
   sequent{ <H> >- col_equal{'T; "union"{'S; s.'c}; 'c}}

(*    ×s:S.(if b then C[s] else D[s]) =
 *    (if b then (×s:S.C[s]) else (×s:S.D[s])) in collection(T)
 *)
interactive union_if  univ[l:l] :
   sequent{ <H> >- "type"{'T}} -->
   sequent{ <H> >- 'S in univ[l:l] } -->
   sequent{ <H>; s:'S >- 'C['s] in col[l:l]{'T} } -->
   sequent{ <H>; s:'S >- 'D['s] in col[l:l]{'T} } -->
   sequent{ <H> >- 'b in bool } -->
   sequent{ <H> >- col_equal{'T; "union"{'S; s. ifthenelse{'b; 'C['s]; 'D['s]}};
                                       ifthenelse{'b; "union"{'S; s. 'C['s]};  "union"{'S; s. 'D['s]}} }}

(*    (c + d) = (d + c) in collection(T)
 *)
interactive add_com univ[l:l] :
   sequent{ <H> >- "type"{'T}} -->
   sequent{ <H> >- 'c in col[l:l]{'T} } -->
   sequent{ <H> >- 'd in col[l:l]{'T} } -->
   sequent { <H> >- col_equal{'T;add{'c;'d};add{'d;'c}}}

(*   (c + <>) = c in collection(T)
 *)
interactive add_none univ[l:l]:
   sequent{ <H> >- "type"{'T}} -->
   sequent{ <H> >- 'c in col[l:l]{'T} } -->
   sequent { <H> >- col_equal{'T;add{'c;none};'c}}

(*   (c + <>) = c in collection(T)
 *)
interactive none_add univ[l:l]:
   sequent{ <H> >- "type"{'T}} -->
   sequent{ <H> >- 'c in col[l:l]{'T} } -->
   sequent { <H> >- col_equal{'T;add{'c;none};'c}}

(*    (c + c) = c in collection(T)
 *)
interactive add_idempotent univ[l:l] :
   sequent{ <H> >- "type"{'T}} -->
   sequent{ <H> >- 'c in col[l:l]{'T} } -->
   sequent { <H> >- col_equal{'T;add{'c;'c};'c}}

(*  <(if b then x else y)> = (if b then <x> else <y>) in collection(T)
 *)
interactive singleton_if  univ[l:l] :
   sequent{ <H> >- 'x in 'T } -->
   sequent{ <H> >- 'y in 'T } -->
   sequent{ <H> >- 'b in bool } -->
   sequent{ <H> >- col_equal{'T; singleton{ ifthenelse{'b;'x;'y}};
                                       ifthenelse{'b; singleton{'x}; singleton{'y}} }}

*)

doc docoff

(********************** Tactics *********************)

let colEqSymT = funT (fun p ->
   col_equal_sym (get_univ_arg p))

let colEqTransT = argfunT (fun t p ->
   col_equal_trans (get_univ_arg p) t)

(********************** dforms **********************)

declare display_col{'T: Dform} : Dform

dform col_df : except_mode[src] :: col[l:l]{'T} =
   `"col[" slot[l:l] `"](" slot{'T} `")"

dform col_df : except_mode[src] :: Col[l:l]{'T} =
   `"Collection[" slot[l:l] `"](" slot{'T} `")"

dform col_member_df : except_mode[src] :: col_member{'C;'x} =
   ('x in 'C)

dform col_equal_df : except_mode[src] :: col_equal{'T;'c_1;'c_2} =
   math_equal{display_col{'T};'c_1;'c_2}

dform display_col_df : display_col{'T} =
   `"collection{" slot{'T} `"}"

dform type_col_df : except_mode[src] :: type_col{'T} = downarrow slot{'T}
dform col_type_df : except_mode[src] :: col_type{'C;'T} = uparrow slot{'C}

dform singleton_df : except_mode[src] ::
   singleton{'x; 'T} = `"<" slot{'x} `">" izone `"_" ezone slot{'T}

dform union_df : except_mode[src] :: parens :: "prec"[prec_tunion] :: "union"{'X; x. 'C} =
   cup slot{'x} `":" slot{'X} `"." slot{'C}

dform col_filter_df : except_mode[src] :: col_filter{'C; x.'P} =
      pushm[3] `"< " bvar{'x} `":" slot{'C} mid slot{'P} `">" popm

dform isect_df : except_mode[src] :: parens :: "prec"[prec_tunion] :: "isect"{'S; s. 'C} =
   cap slot{'s} `":" slot{'S} `"." slot{'C}

dform none_df : except_mode[src] :: none = `"<>"

dform add_df : except_mode[src] :: parens :: "prec"[prec_add] :: "add"{'a; 'b} =
   slot["le"]{'a} `" + " slot["lt"]{'b}
