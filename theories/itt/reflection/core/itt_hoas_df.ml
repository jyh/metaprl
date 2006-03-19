doc <:doc<
   @module[Itt_hoas_df]
   The @tt[Itt_hoas_df] module defines some display forms for
   reflected terms.x

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2005-2006, MetaPRL Group

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
extends Itt_hoas_base
extends Itt_hoas_operator
extends Itt_hoas_debruijn

open Basic_tactics

open Lm_printf

open Dform

open Itt_list
open Itt_hoas_base
open Itt_hoas_operator
open Itt_hoas_debruijn

type ('a, 'b) option2 =
   Some1 of 'a
 | Some2 of 'b

(************************************************************************
 * Utilities.
 *)
exception BadShape

declare unquote{'t}

dform unquote_df : unquote{'t} =
   `"$,(" 't `")"

let unquote_term = << unquote{'t} >>
let unquote_opname = opname_of_term unquote_term
let mk_unquote_term =
   mk_dep0_term unquote_opname

(************************************************************************
 * For general mk_term, try unquoting and using the original
 * display forms.
 *)
declare raw_mk_term{'op; 'subterms}

dform raw_mk_term_df : raw_mk_term{'op; 'subterms} =
   szone pushm[3]
      `"Term(" slot{'op} `"," hspace slot{'subterms} `")"
   popm ezone

let raw_mk_term_term = << raw_mk_term{'op; 'subterms} >>
let raw_mk_term_opname = opname_of_term raw_mk_term_term
let mk_raw_mk_term_term =
   mk_dep0_dep0_term raw_mk_term_opname

module MkTerm =
struct
   (*
    * Term unquoting.
    *)
   let rec unquote_term_exn op subterms =
      let { opparam_name = opname;
            opparam_params = params;
            opparam_arities = arities
          } = dest_operator_term op
      in
      let subterms = dest_list_term subterms in
      let bterms = unquote_subterms_exn arities subterms in
      let op = mk_op opname params in
         mk_term op bterms

   and unquote_subterms_exn arities subterms =
      match arities, subterms with
         arity :: arities, subterm :: subterms ->
            unquote_subterm_exn arity subterm :: unquote_subterms_exn arities subterms
       | [], [] ->
            []
       | _ :: _, []
       | [], _ :: _ ->
            raise BadShape

   and unquote_subterm_exn arity t =
      let vars, t = unquote_bind_arity_exn arity [] t in
         mk_bterm vars t

   and unquote_bind_arity_exn arity vars t =
      if arity = 0 then
         List.rev vars, unquote_mk_term t
      else
         let v, t = dest_bind_term t in
            unquote_bind_arity_exn (pred arity) (v :: vars) t

   and unquote_mk_term t =
      let info =
         try Some (dest_mk_term_term t) with
            RefineError _ ->
               None
      in
         match info with
            Some (op, subterms) ->
               (try unquote_term_exn op subterms with
                   RefineError _
                 | BadShape ->
                      mk_raw_mk_term_term op subterms)
          | None ->
               mk_unquote_term t

   (*
    * The display form.
    *)
   let display_mk_term format_term buf op subterms =
      let t =
         try Some1 (unquote_term_exn op subterms) with
            RefineError _
          | BadShape ->
               Some2 (mk_raw_mk_term_term op subterms)
      in
         match t with
            Some1 t ->
               Lm_rformat.format_string buf "$`(";
               format_term buf NOParens t;
               Lm_rformat.format_string buf ")"
          | Some2 t ->
               format_term buf LEParens t
end;;

ml_dform mk_term_df : mk_term{'op; 'subterms} format_term buf = fun _ ->
   MkTerm.display_mk_term format_term buf op subterms

(************************************************************************
 * Displaying mk_bterm is similar, but we require that the depths match.
 *)
declare raw_mk_bterm{'n; 'op; 'subterms}

dform raw_mk_bterm_df : raw_mk_bterm{'n; 'op; 'subterms} =
   szone pushm[3]
      `"BTerm(" slot{'n} `"," hspace slot{'op} `"," hspace slot{'subterms} `")"
   popm ezone

let raw_mk_bterm_term = << raw_mk_bterm{'n; 'op; 'subterms} >>
let raw_mk_bterm_opname = opname_of_term raw_mk_bterm_term
let mk_raw_mk_bterm_term =
   mk_dep0_dep0_dep0_term raw_mk_bterm_opname

module MkBTerm =
struct
   (*
    * Term unquoting.
    *)
   let rec unquote_bterm_exn n op subterms =
      let { opparam_name = opname;
            opparam_params = params;
            opparam_arities = arities
          } = dest_operator_term op
      in
      let subterms = dest_list_term subterms in
      let bterms = unquote_subterms_exn n arities subterms in
      let op = mk_op opname params in
         mk_term op bterms

   and unquote_subterms_exn n arities subterms =
      match arities, subterms with
         arity :: arities, subterm :: subterms ->
            unquote_subterm_exn n arity subterm :: unquote_subterms_exn n arities subterms
       | [], [] ->
            []
       | _ :: _, []
       | [], _ :: _ ->
            raise BadShape

   and unquote_subterm_exn n arity t =
      let vars, t = unquote_bind_arity_exn n arity [] t in
         mk_bterm vars t

   and unquote_bind_arity_exn n arity vars t =
      if arity = 0 then
         List.rev vars, unquote_mk_bterm n t
      else
         let v, t = dest_bind_term t in
            unquote_bind_arity_exn n (pred arity) (v :: vars) t

   and unquote_mk_bterm n t =
      let info =
         try Some (dest_mk_bterm_term t) with
            RefineError _ ->
               None
      in
         match info with
            Some (d, op, subterms) ->
               (try unquote_bterm_exn n op subterms with
                   RefineError _
                 | BadShape ->
                      mk_raw_mk_bterm_term n op subterms)
          | None ->
               mk_unquote_term t

   (*
    * The display form.
    *)
   let display_mk_bterm format_term buf n op subterms =
      let t =
         try Some1 (unquote_bterm_exn n op subterms) with
            RefineError _
          | BadShape ->
               Some2 (mk_raw_mk_bterm_term n op subterms)
      in
         match t with
            Some1 t ->
               Lm_rformat.format_string buf "$'[";
               format_term buf NOParens n;
               Lm_rformat.format_string buf "](";
               format_term buf NOParens t;
               Lm_rformat.format_string buf ")"
          | Some2 t ->
               format_term buf LEParens t
end;;

ml_dform mk_bterm_df : mk_bterm{'n; 'op; 'subterms} format_term buf = fun _ ->
   MkBTerm.display_mk_bterm format_term buf n op subterms

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
