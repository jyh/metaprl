(*
 * Compute the free vars of a term.
 * This is all the lids.
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
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)

open Lm_debug
open Lm_printf

(*
 * Show the file loading.
 *)
let _ =
   show_loading "Loading Free_vars%t"


(*
 * Compute the binding variables.
 *)
(*
 * camlp5 8 replaced the old PaAcc/PaUid with PaPfx (M.p) and PaLong
 * (a possibly qualified constructor).  The cases below give the results
 * the old ones did: a prefix binds what its pattern binds, and a
 * constructor binds nothing.
 *)
let rec patt_bvars bvars = function
   MLast.PaPfx (_, _, p) ->
      patt_bvars bvars p
 | MLast.PaLong (_, _, Ploc.VaVal []) ->
      bvars
 | <:patt< ($p1$ as $p2$) >>
 | <:patt< $p1$ $p2$ >>
 | <:patt< $p1$ | $p2$ >>
 | <:patt< $p1$ .. $p2$ >> ->
      patt_bvars (patt_bvars bvars p1) p2
 | <:patt< _ >>
 | <:patt< $chr:_$ >>
 | <:patt< $int:_$ >>
 | <:patt< $str:_$ >> ->
      bvars
 | <:patt< $lid:i$ >> ->
      if List.mem i bvars then
         bvars
      else
         i :: bvars
 | <:patt< { $list:ppl$ } >> ->
      List.fold_left (fun bvars (p1, p2) -> patt_bvars (patt_bvars bvars p1) p2) bvars ppl
 | <:patt< ( $list:pl$ ) >> ->
      List.fold_left patt_bvars bvars pl
 | <:patt< ( $p$ : $_$ ) >> ->
      patt_bvars bvars p
   (* Variant tags, int32/int64/nativeint literals and first-class module
    * patterns bind no value names; an array binds what its items bind. *)
 | MLast.PaVrn _
 | MLast.PaInt _
 | MLast.PaUnp _ ->
      bvars
 | MLast.PaArr (_, Ploc.VaVal pl) ->
      List.fold_left patt_bvars bvars pl
 | _ ->
      raise (Failure "patt_bvars: pattern not recognized")

let patt_vars patt =
   patt_bvars [] patt

(*
 * Compute free vars of an Ast.expr.
 *)
let free_vars expr =
   (*
    * camlp5 8 replaced the old ExAcc/ExUid with ExLong (a module or
    * constructor path), ExFle (e.f and e.M.f) and ExOpen (M.(e)), and
    * index expressions now carry a list of indices.  Each case below
    * gives the result the old one did: a path contributes nothing, the
    * field name of e.f is treated like a variable (as the old ExAcc case
    * did), and M.(e) is e.
    *)
   let add bvars l v =
      if List.mem v bvars || List.mem v l then
         l
      else
         v :: l
   in
   let rec free bvars l = function
      <:expr< $lid:v$ >> ->
         add bvars l v
    | MLast.ExFle (_, e, Ploc.VaVal (_, Ploc.VaVal f)) ->
         add bvars (free bvars l e) f
    | MLast.ExLong _ ->
         l
    | MLast.ExOpen (_, _, e) ->
         free bvars l e
    | MLast.ExAre (_, _, e, Ploc.VaVal il)
    | MLast.ExSte (_, _, e, Ploc.VaVal il) ->
         List.fold_left (free bvars) l (e :: il)
    | <:expr< $e1$ $e2$ >>
    | <:expr< $e1$ := $e2$ >> ->
         free bvars (free bvars l e1) e2
    | <:expr< [| $list:el$ |] >>
    | <:expr< do { $list:el$ } >>
    | <:expr< ( $list:el$ ) >> ->
         List.fold_left (free bvars) l el
    | <:expr< $chr:_$ >>
    | <:expr< $flo:_$ >>
    | <:expr< $int:_$ >>
    | <:expr< $str:_$ >> ->
         l
(*
    | <:expr< ( $e1$ :> $_$ ) >> ->
*)
    | MLast.ExCoe (_, e, _, _)
    | <:expr< $e$ # $_$ >>
    | MLast.ExLSI (_, Ploc.VaVal (MLast.StMod _), e)
    | <:expr< ( $e$ : $_$ ) >> ->
         free bvars l e
    | MLast.ExFor (_, p, e1, e2, _, Ploc.VaVal el) ->
         List.fold_left (free (patt_bvars bvars p)) (free bvars (free bvars l e1) e2) el
    | <:expr< fun [ $list:pwel$ ] >> ->
         free_pwel bvars l pwel
    | <:expr< if $e1$ then $e2$ else $e3$ >> ->
         free bvars (free bvars (free bvars l e1) e2) e3
    | MLast.ExLet (_, rf, Ploc.VaVal pel, e) ->
         (* The names a let binds are bound in its body, and in the
          * right-hand sides only when it is recursive. *)
         let bvars' = List.fold_left (fun bvars (p, _, _) -> patt_bvars bvars p) bvars pel in
         let rhs_bvars = if rf = Ploc.VaVal true then bvars' else bvars in
         let l = List.fold_left (fun l (_, e, _) -> free rhs_bvars l e) l pel in
            free bvars' l e
    | <:expr< match $e$ with [ $list:pwel$ ] >>
    | <:expr< try $e$ with [ $list:pwel$ ] >> ->
         free_pwel bvars (free bvars l e) pwel
    | MLast.ExNew _ ->
         (* As in the old code, this returns bvars, not l. *)
         bvars
    | <:expr< {< $list:sel$ >} >> ->
         List.fold_left (fun l (_, el) -> free bvars l el) l sel
    | <:expr< { $list:eel$ } >> ->
         List.fold_left (fun l (_, el) -> free bvars l el) l eel
    | <:expr< while $e$ do { $list:el$ } >> ->
         List.fold_left (free bvars) (free bvars l e) el
    | MLast.ExRec (_, Ploc.VaVal eel, Some e) ->
         (* { e with f = e1; ... } *)
         List.fold_left (fun l (_, e) -> free bvars l e) (free bvars l e) eel
    | MLast.ExLab (_, _, Ploc.VaVal (Some e)) ->
         free bvars l e
    | MLast.ExLab (_, MLast.PaLid (_, Ploc.VaVal v), Ploc.VaVal None) ->
         (* ~v, a punned label, is the variable v *)
         add bvars l v
    | MLast.ExLaz (_, e)
    | MLast.ExAsr (_, e)
    | MLast.ExLSI (_, Ploc.VaVal (MLast.StOpn _), e) ->
         free bvars l e
    | MLast.ExInt _ ->
         (* int32, int64 and nativeint literals *)
         l
    | MLast.ExObj (_, Ploc.VaVal po, Ploc.VaVal cfl) ->
         free_obj bvars l po cfl
    | _ ->
         raise (Failure "free_vars: expression not recognized")
   (*
    * An object: its instance variables and its self pattern are bound in
    * its methods and initializers, not in the instance variables' own
    * initial values.  An inherit brings in names this cannot see.
    *)
   and free_obj bvars l po cfl =
      let rec ivars vl = function
         MLast.CrVal (_, _, _, Ploc.VaVal v, _, _) -> v :: vl
       | MLast.CrDcl (_, Ploc.VaVal cfl) -> List.fold_left ivars vl cfl
       | _ -> vl
      in
      let inner = List.fold_left ivars (match po with Some p -> patt_bvars bvars p | None -> bvars) cfl in
      let rec item l = function
         MLast.CrVal (_, _, _, _, e, _) -> free bvars l e
       | MLast.CrMth (_, _, _, _, _, e, _)
       | MLast.CrIni (_, e, _) -> free inner l e
       | MLast.CrDcl (_, Ploc.VaVal cfl) -> List.fold_left item l cfl
       | MLast.CrVav _ | MLast.CrVir _ | MLast.CrFlAtt _ | MLast.CrExten _ -> l
       | _ -> raise (Failure "free_vars: object item not recognized")
      in
         List.fold_left item l cfl
   and free_pwel bvars l = function
      (patt, guard, e)::tl ->
          (* A case binds its pattern's variables in its guard and body. *)
          let bvars' = patt_bvars bvars patt in
          let l =
             match guard with
                Ploc.VaVal (Some g) -> free bvars' l g
              | _ -> l
          in
             free_pwel bvars (free bvars' l e) tl
     | [] ->
          l
   in
      free [] [] expr

let _ = ()

(*
 * Find some new variable names.
 *)
let new_vars expr l =
   let free = free_vars expr in
   let rec new_var i v =
      let vname = sprintf "%s%d" v i in
         if List.mem vname free then
            new_var (i + 1) v
         else
            vname
   in
      List.map (new_var 0) l

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
