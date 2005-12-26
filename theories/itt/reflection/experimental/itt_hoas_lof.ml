doc <:doc<
   @module[Itt_hoas_lof]

   During normalization, we define a custom version of list_of_fun.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2005, MetaPRL Group

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

   Author: Jason Hickey @email{jyh@cs.caltech.edu}

   @end[license]
   @parents
>>
extends Itt_list3
extends Itt_hoas_vector

doc docoff

open Basic_tactics

(************************************************************************
 * Normalization for list_of_fun.
 *)
doc <:doc<
   We use << list_of_fun{i. 'f['i]; 'n} >> to normalize nested substitutions.
   We define a stylized version << lof{i. 'f['i]; 'n} >> to make the work easier.
>>
define unfold_bindN : bindn{'n; x. 'e['x]} <-->
   bind{'n; x. 'e['x]}

define unfold_lof : lof{i. 'f['i]; 'n} <-->
   list_of_fun{i. 'f['i]; 'n}

doc <:doc<
   In the stylized version << lof{i. 'f['i]; 'n} >>, define some expressions
   for << 'f['i] >>.
>>
define unfold_lof_nth : lof_nth{'x; 'i} <-->
   nth{'x; 'i}

interactive_rw bindn_to_lof :
   'n in nat -->
   bind{'n; x. 'e['x]}
   <-->
   bindn{'n; x. 'e[lof{i. lof_nth{'x; 'i}; 'n}]}

doc <:doc<
   The << lof{i. 'f['i]; 'n} >> normalizers follow the same pattern as in Itt_list3.
   @docoff
>>
let extract_data tbl =
   let rw t =
      let conv =
         try
            (* Find and apply the right tactic *)
            Term_match_table.lookup tbl select_all t
         with
            Not_found ->
               raise (RefineError ("Conversionals.extract_data", StringTermError ("no reduction for", t)))
      in
         conv
   in
      termC rw

let process_normalize_lof_resource_rw_annotation = redex_and_conv_of_rw_annotation "normalize_lof"

(*
 * Resource.
 *)
let resource (term * conv, conv) normalize_lof =
   table_resource_info extract_data

let normalizeLofTopC_env e =
   get_resource_arg (env_arg e) get_normalize_lof_resource

let normalizeLofTopC = funC normalizeLofTopC_env

let normalizeLofC =
   funC (fun e -> repeatC (higherC (normalizeLofTopC_env e)))

let normalizeLofT =
   rwAll normalizeLofC

(************************************************************************
 * Normalization rules.
 *)
doc <:doc<
   Normalization rules.
>>
interactive_rw nth_prefix_lof {| normalize_lof |} :
   'n in nat -->
   'm in nat -->
   'm <= 'n -->
   nth_prefix{lof{i. 'f['i]; 'n}; 'm}
   <-->
   lof{i. 'f['i]; 'm}

interactive_rw nth_suffix_lof {| normalize_lof |} :
   'n in nat -->
   'm in nat -->
   'm <= 'n -->
   nth_suffix{lof{i. 'f['i]; 'n}; 'm}
   <-->
   lof{i. 'f['i +@ 'm]; 'n -@ 'm}

interactive_rw hd_lof {| normalize_lof |} :
   'n in nat -->
   not{'n = 0 in nat} -->
   hd{lof{i. 'f['i]; 'n}}
   <-->
   'f[0]

interactive_rw tl_lof {| normalize_lof |} :
   'n in nat -->
   not{'n = 0 in nat} -->
   tl{lof{i. 'f['i]; 'n}}
   <-->
   lof{i. 'f['i +@ 1]; 'n -@ 1}

interactive_rw singleton_lof {| normalize_lof |} :
   cons{'e; nil}
   <-->
   lof{i. 'e; 1}

interactive_rw cons_lof {| normalize_lof |} :
   'n in nat -->
   cons{'e; lof{i. 'f['i]; 'n}}
   <-->
   lof{i. if beq_int{'i; 0} then 'e else 'f['i -@ 1]; 'n +@ 1}

interactive_rw append_lof {| normalize_lof |} :
   'm in nat -->
   'n in nat -->
   append{lof{k. 'f['k]; 'm}; lof{k. 'g['k]; 'n}}
   <-->
   lof{k. if lt_bool{'k; 'm} then 'f['k] else 'g['k -@ 'm]; 'm +@ 'n}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
