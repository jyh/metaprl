(* File_base (mllib), the store of a theory's compiled files in their
   several formats, which the proof census uses at every load and no unit
   test drove (2026-11-11 reach census: 6 lines).  A base over three
   format specs, all reading and writing a file's whole contents:
     A, suffix ".fa"      A, suffix ".fa2" (disabled)      B, suffix ".fb"
   in a fresh temporary directory holding m.fa, m.fa2 and m.fb.  Each line
   prints what find, find_file and find_match return (the format, the
   file and its contents) or the exception, after the operations before
   it, so the base's memory of what it loaded is part of what is shown:
   find returns a module the base already holds in the requested format
   and otherwise loads it; find_match finds the same module in another
   format; a disabled spec is never read; OnlySuffixes restricts the
   specs; a format with no spec is refused.  A refusal's message names
   the temporary directory, so only its first line is printed. *)
type select = A | B | C

module Info = struct
  type nonrec select = select
  type cooked = string
  type arg = unit
  let read f = let ic = open_in_bin f in let n = in_channel_length ic in let s = really_input_string ic n in close_in ic; s
  let spec select suffix disabled = {
    File_base_type.info_marshal = (fun _ _ _ () f s -> let oc = open_out_bin f in output_string oc s; close_out oc);
    info_unmarshal = (fun _ _ () f -> read f, 0);
    info_disabled = ref disabled; info_select = select; info_suffix = suffix; info_magics = [ 0 ]; info_versions = [ 0 ] }
  let info = [ spec A "fa" false; spec A "fa2" true; spec B "fb" false ]
end
module FB = File_base.MakeFileBase (Info)

let sel = function A -> "A" | B -> "B" | C -> "C"
let dir = Filename.concat (Filename.get_temp_dir_name ()) (Printf.sprintf "test_file_base_%d" (Unix.getpid ()))
let () =
  Unix.mkdir dir 0o755;
  List.iter (fun (n, s) -> let oc = open_out_bin (Filename.concat dir n) in output_string oc s; close_out oc)
    [ "m.fa", "A text"; "m.fa2", "A2 text"; "m.fb", "B text"; "n.fb", "B of n" ]

let show base i = Printf.sprintf "%s %s %S" (sel (FB.type_of base i)) (FB.file_name base i) (FB.info base i)
let line name f = Printf.printf "%-44s %s\n" name (try f () with Failure s -> "Failure: " ^ List.hd (String.split_on_char '\n' s) ^ " (the search path follows)" | Invalid_argument s -> "Invalid_argument: " ^ s | Not_found -> "Not_found")

let () =
  let base = FB.create [ dir ] in
  let ia = ref None in
  line "find m A" (fun () -> let i = FB.find base () "m" A File_base_type.AnySuffix in ia := Some i; show base i);
  line "find m A again" (fun () -> show base (FB.find base () "m" A File_base_type.AnySuffix));
  line "find m B (m held as A)" (fun () -> show base (FB.find base () "m" B File_base_type.AnySuffix));
  line "find_match (m A) B (held)" (fun () -> show base (FB.find_match base () (Option.get !ia) B File_base_type.AnySuffix));
  line "find m A, OnlySuffixes [fa2] (disabled)" (fun () -> show base (FB.find_file base () "m" A (File_base_type.OnlySuffixes [ "fa2" ])));
  line "find m C (no spec)" (fun () -> show base (FB.find base () "m" C File_base_type.AnySuffix));
  line "find_file m B, OnlySuffixes [fb]" (fun () -> show base (FB.find_file base () "m" B (File_base_type.OnlySuffixes [ "fb" ])));
  let base2 = FB.create [ dir ] in
  line "base 2: find n B" (fun () -> show base2 (FB.find base2 () "n" B File_base_type.AnySuffix));
  line "base 2: find m A, then find_match B (loads)" (fun () ->
      let i = FB.find base2 () "m" A File_base_type.AnySuffix in show base2 (FB.find_match base2 () i B File_base_type.AnySuffix));
  line "base 2: find_match (m A) B again (held)" (fun () ->
      let i = FB.find base2 () "m" A File_base_type.AnySuffix in show base2 (FB.find_match base2 () i B File_base_type.AnySuffix));
  line "base 2: find q A (no file)" (fun () -> show base2 (FB.find base2 () "q" A File_base_type.AnySuffix));
  List.iter (fun n -> Sys.remove (Filename.concat dir n)) [ "m.fa"; "m.fa2"; "m.fb"; "n.fb" ];
  Unix.rmdir dir
