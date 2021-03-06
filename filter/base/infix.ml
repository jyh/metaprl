(*
 * This file just exists to extract the code for adding and infix
 * expression.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
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
 * Author: Jason Hickey <jyh@cs.cornell.edu>
 * Modified By: Aleksey Nogin <nogin@cs.caltech.edu>
 *)

open Pcaml
open Filter_type

(*
 * The prefix version of the infix expression
 *)
let prefix_name op = "prefix_" ^ op

(*
 * Add an infix keyword.
 *)
let add_infix (keyword : string) =
  Grammar.extend
    (let _ = (expr : 'expr Grammar.Entry.e) in
     [Grammar.Entry.obj (expr : 'expr Grammar.Entry.e),
      Some (Gramext.Level "expr1"),
      [Some "expr1", Some Gramext.LeftA,
       [[Gramext.Sself; Gramext.Stoken ("", keyword); Gramext.Sself],
        Gramext.action
          (fun (e2 : 'expr) (op : string) (e1 : 'expr) (_loc : Ploc.t) ->
             (MLast.ExApp
                (_loc,
                 MLast.ExApp
                   (_loc, MLast.ExLid (_loc, Ploc.VaVal (prefix_name op)),
                    e1),
                 e2) :
              'expr))]]])

(*
 * Remove the infix keyword.
 *)
let remove_infix (keyword : string) =
  Grammar.delete_rule expr
    [Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e));
     Gramext.Stoken ("", keyword);
     Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e))]

(*
 * Add an suffix keyword.
 *)
let add_suffix (keyword : string) =
  Grammar.extend
    (let _ = (expr : 'expr Grammar.Entry.e) in
     [Grammar.Entry.obj (expr : 'expr Grammar.Entry.e),
      Some (Gramext.Level "expr1"),
      [Some "expr1", Some Gramext.LeftA,
       [[Gramext.Sself; Gramext.Stoken ("", keyword)],
        Gramext.action
          (fun (op : string) (e : 'expr) (_loc : Ploc.t) ->
             (MLast.ExApp
                (_loc, MLast.ExLid (_loc, Ploc.VaVal (prefix_name op)), e) :
              'expr))]]])

(*
 * Remove the suffix keyword.
 *)
let remove_suffix (keyword : string) =
  Grammar.delete_rule expr
    [Gramext.Snterm (Grammar.Entry.obj (expr : 'expr Grammar.Entry.e));
     Gramext.Stoken ("", keyword)]

let add =
  function
    Infix s -> add_infix s
  | Suffix s -> add_suffix s

let remove =
  function
    Infix s -> remove_infix s
  | Suffix s -> remove_suffix s

module SetBase =
  struct
    type t = grammar_update
    let compare = Pervasives.compare
  end

module Set = Lm_set.LmMake (SetBase)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
