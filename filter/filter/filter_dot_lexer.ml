(*
 * camlp5 8 lexes OCaml's dot operators (OCaml 4.06: ".^", ".+", ".%{" ...)
 * as one token: ".^data" is ".^" then "data". camlp5 7 had no such rule,
 * so it lexed "." and then the operator: "." "^" "data". MetaPRL term
 * syntax depends on the camlp5 7 form; ".^data" is the field data of self
 * in theories/itt/applications/datatypes (6 sites). Lexing every theory
 * source with both versions, outside doc text, finds no other difference
 * of this kind.
 *
 * split wraps a lexer so that each such token is returned as "." and then
 * the rest, with the location of each part. No other token is changed.
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
 *)

(* The characters camlp5 8's Plexer accepts after the dot of a dot operator. *)
let is_dot_symbol c =
   String.contains "!$%&*+-/:=>?@^|" c

let is_dot_operator s =
   String.length s >= 2 && s.[0] = '.' && is_dot_symbol s.[1]

let split (lexer : (string * string) Plexing.lexer) =
   let tok_func cs =
      let strm, loc = lexer.Plexing.tok_func cs in
      let locs = Plexing.Locations.create () in
      let pending = Queue.create () in
      let count = ref 0 in
      let next i =
         let item =
            if not (Queue.is_empty pending) then
               Some (Queue.pop pending)
            else
               match Stream.peek strm with
                  None ->
                     None
                | Some tok ->
                     Stream.junk strm;
                     let l = Plexing.Locations.lookup loc !count in
                        incr count;
                        match tok with
                           ("", s) when is_dot_operator s ->
                              let n = String.length s - 1 in
                                 Queue.push (("", String.sub s 1 n), Ploc.sub l 1 n) pending;
                                 Some (("", "."), Ploc.sub l 0 1)
                         | _ ->
                              Some (tok, l)
         in
            match item with
               Some (tok, l) ->
                  Plexing.Locations.add locs i l;
                  Some tok
             | None ->
                  None
      in
         Stream.from next, locs
   in
      { lexer with Plexing.tok_func = tok_func }

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
