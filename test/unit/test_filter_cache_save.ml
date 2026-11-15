(* unit-link: filter *)
(* Filter_cache's ASCII save (the shell's export, Package_info.save_aux
   "prla"): StrFilterCache.save with OnlySuffixes ["prla"] goes through
   Filter_cache.AsciiIO.write, which first reads the file it is about to
   replace (Ascii_io.read_table, which only collects the lines) so the new
   file can reuse its names, starting from an empty table when that read
   fails, then opens m.prla.new and writes the term with that table.  No unit test built a
   cache before this one.  Each case saves an empty module m, damages m.prla, and saves again, printing whether
   the save returned or raised, m.prla's first line and line count,
   whether a file descriptor was left open, and whether m.prla.new was
   left behind.  Writing with the old table decodes its entries
   (Ascii_io.output_term, after dropping duplicate lines), so an entry that
   names an undefined term raises Invalid_argument there, after m.prla.new
   was opened: write lets it out, the channel is never closed and the
   .new file stays.  A file with no header or a newer version is refused
   (Bad_magic, Bad_version) before anything is opened for writing.  The expected file is the
   output of the code as written, never typed. *)
open File_base_type
open Filter_summary_type

module C = Filter_cache.MakeCaches (Proof_convert.Convert)
module S = C.StrFilterCache

(* create_cache puts a new module in the current directory (run.sh runs
   each test in a fresh temporary one), whatever the cache's path. *)
let file = "m.prla"

let lines_of f = let ic = open_in_bin f in
  let rec go acc = match input_line ic with l -> go (l :: acc) | exception End_of_file -> List.rev acc in
  let l = go [] in close_in ic; l
let write_lines f l = let oc = open_out_bin f in List.iter (fun s -> output_string oc s; output_char oc '\n') l; close_out oc

(* The next descriptor the system hands out: a read that leaks one moves it
   up by one.  On Windows a descriptor is a handle, not a small integer, so
   this prints "not measured" there; the leak shows instead as a refusal to
   remove m.prla.new (test_filter_cache_save.expected.win32). *)
let next_fd () =
  let fd = Unix.openfile Filename.null [ Unix.O_RDONLY ] 0 in
  let n = if Sys.os_type = "Unix" then (Obj.magic fd : int) else 0 in
  Unix.close fd; n

let save () =
  let cache = S.create [ "." ] in
  let info = S.create_cache cache "m" ImplementationType in
  S.set_mode info InteractiveSummary;
  S.save info () (OnlySuffixes [ "prla" ])

let case name damage =
  write_lines file damage;
  let before = next_fd () in
  let result = try save (); "returned" with e -> "raised " ^ Printexc.to_string e in
  let after = next_fd () in
  let l = lines_of file in
  Printf.printf "%-34s save %s\n" name result;
  Printf.printf "%-34s   file: %d lines, first %S\n" "" (List.length l) (List.hd l);
  Printf.printf "%-34s   descriptor left open: %s\n" ""
    (if Sys.os_type <> "Unix" then "not measured on this system" else if after > before then "yes" else "no");
  Printf.printf "%-34s   m.prla.new left behind: %b\n" "" (Sys.file_exists (file ^ ".new"));
  (* An open handle keeps Windows from removing the file. *)
  if Sys.file_exists (file ^ ".new") then
    Printf.printf "%-34s   removing m.prla.new: %s\n" ""
      (try Sys.remove (file ^ ".new"); "done" with Sys_error e -> "refused, " ^ e)

let () =
  save ();
  let lines = lines_of file in
  Printf.printf "first save: %d lines, first %S\n" (List.length lines) (List.hd lines);
  List.iter (fun l -> Printf.printf "  %S\n" l) (List.tl lines);
  let body = List.tl lines in
  let header = List.hd lines in
  let field1 l = match String.split_on_char '\t' l with _ :: n :: _ -> n | _ -> "" in
  let named = List.filter (fun l -> field1 l <> "") body in
  let last = List.nth named (List.length named - 1) in
  case "the file as saved" lines;
  case "no header line" body;
  case "a newer version in the header" ("#PRL version 99.0.0 ASCII term" :: body);
  case "the last entry (the root) doubled" (lines @ [ last ]);
  case "the O entry doubled" (List.concat_map (fun l -> if l.[0] = 'O' then [ l; l ] else [ l ]) lines);
  case "an entry naming an undefined term" (header :: body @ [ "T\tzz\tundefined_name" ])
