(* unit-link: filter *)
(*
 * Filter_buffer (filter/base), a growable byte buffer: putc, puts,
 * gets and clear, below the initial 32 bytes and past them.
 *
 * Nothing in the tree uses this module, and no build or census reaches
 * past its first line.
 *
 * The expected file is the output of the code.  Before the fix that
 * followed this test, putc and puts grew the buffer and then wrote into
 * the old one, so the first write past 32 bytes raised Invalid_argument
 * (the 2026-10-27 port to Bytes, b8657296c, kept that and said so).
 *)
let try_ name f =
   match f () with
      s -> Printf.printf "  %-34s %S\n" name s
    | exception Invalid_argument _ -> Printf.printf "  %-34s raised Invalid_argument\n" name

let () =
   let b = Filter_buffer.create () in
      try_ "empty" (fun () -> Filter_buffer.gets b);
      try_ "putc a, puts \"bc\"" (fun () -> Filter_buffer.putc b 'a'; Filter_buffer.puts b "bc"; Filter_buffer.gets b);
      try_ "clear" (fun () -> Filter_buffer.clear b; Filter_buffer.gets b);
      try_ "puts 32 bytes (exactly full)" (fun () -> Filter_buffer.puts b (String.make 32 'x'); String.length (Filter_buffer.gets b) |> string_of_int);
      try_ "then putc (past 32)" (fun () -> Filter_buffer.putc b 'y'; Filter_buffer.gets b |> String.length |> string_of_int);
   let b = Filter_buffer.create () in
      try_ "puts 40 bytes into an empty buffer" (fun () -> Filter_buffer.puts b (String.make 40 'z'); Filter_buffer.gets b);
   let b = Filter_buffer.create () in
      try_ "putc 33 times" (fun () -> for i = 0 to 32 do Filter_buffer.putc b (Char.chr (65 + i mod 26)) done; Filter_buffer.gets b);
   let b = Filter_buffer.create () in
      try_ "puts 20 + 20 + 30" (fun () -> List.iter (fun n -> Filter_buffer.puts b (String.make n '.')) [20; 20; 30];
                                         Filter_buffer.gets b |> String.length |> string_of_int)
