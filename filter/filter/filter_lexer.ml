(*
 * The lexer for MetaPRL's term grammar, on camlp5 8.
 *
 * MetaPRL writes {| ... |} as brackets (resource annotations, sequents),
 * 6,894 times in theories/. camlp5 8's pa_o makes the lexer with
 * Plexer.simplest_raw_strings set, so {|...|} lexes as an OCaml quoted
 * string, and the keyword "{|" is refused. camlp5 7's lexer had no quoted
 * strings. install puts in a lexer made with that flag unset, before the
 * term grammar adds its rules. $ antiquotations stay on: pa_o turns them
 * off, but <:con< ... $x$ ... >> quotations need them (with them off, three
 * of the sixteen support/display files fail to preprocess). The lexer also
 * splits camlp5 8's dot-operator tokens back into "." and the operator, as
 * camlp5 7 lexed them (Filter_dot_lexer).
 *
 * Grammar.Unsafe.gram_reinit would do this but also empties the grammar's
 * token use counts, and Grammar.delete_rule (Infix, pa_macro) then fails
 * or removes keywords still in use. So the lexer field is set directly
 * (Grammar.g is Gramext.grammar on (string * string) tokens), the counts
 * are kept, and every token in use is registered with the new lexer.
 *
 * Term_grammar.MakeTermGrammar calls install, so every program that builds
 * the term grammar gets this lexer: the filter (filter_parse), prlc
 * (filter_reflect) and the MetaPRL shell (shell_state). It is a call, not
 * a load-time action, because pa_o resets the lexer when it loads and this
 * module is linked before pa_o in the filter. The first call installs;
 * later calls do nothing.
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

let installed = ref false

let install () =
   if not !installed then begin
      installed := true;
      let g = (Obj.magic Pcaml.gram : (string * string) Gramext.grammar) in
      let srs = !Plexer.simplest_raw_strings in
      let dfa = !Plexer.dollar_for_antiquotation in
      let lexer =
         Plexer.simplest_raw_strings := false;
         Plexer.dollar_for_antiquotation := true;
         Fun.protect (**)
            ~finally:(fun () ->
                  Plexer.simplest_raw_strings := srs;
                  Plexer.dollar_for_antiquotation := dfa)
            Plexer.gmake
      in
      let lexer = Filter_dot_lexer.split lexer in
         Hashtbl.iter (fun tok _ -> lexer.Plexing.tok_using tok) g.Gramext.gtokens;
         g.Gramext.glexer <- lexer
   end

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
