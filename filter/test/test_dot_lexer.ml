(*
 * Print every token of each file with its character positions, using the
 * lexer Dot_lexer_compat.make returns. Built against camlp5 7 with
 * dot_lexer_compat_7.ml it prints the camlp5 7 reference; against camlp5 8
 * with dot_lexer_compat_8.ml it prints what filter_parse's lexer returns.
 * test_dot_lexer.expected is the camlp5 7 output for dot_lexer_corpus.txt.
 *)
let () =
   let lexer = Dot_lexer_compat.make () in
   for i = 1 to Array.length Sys.argv - 1 do
      let ic = open_in_bin Sys.argv.(i) in
      let s = really_input_string ic (in_channel_length ic) in
      let () = close_in ic in
      let strm, loc = lexer.Plexing.tok_func (Stream.of_string s) in
      let n = ref 0 in
      let fin = ref false in
         while not !fin do
            let (k, v) = Stream.next strm in
            let l = Dot_lexer_compat.lookup loc !n in
               incr n;
               Printf.printf "%s %S %d %d\n" k v (Ploc.first_pos l) (Ploc.last_pos l);
               if k = "EOI" then fin := true
         done
   done
