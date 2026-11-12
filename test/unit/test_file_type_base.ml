(* File_type_base (mllib), the archive format under every compiled theory
   file: MakeSingletonCombo writes a magic number, a version and the
   marshalled value, and reads them back with checks.  The proof census
   runs it at every load and no unit test did (2026-11-12 census at one
   sha: 12 lines; with them 28 lines no run had reached).  A file base over
   one combo (magics 0x111, 0x222; versions 5, 4) in a fresh temporary
   directory: each line prints the result or the exception and the header
   on disk.  The expected file is the output of the code as written
   (2026-11-12), never typed.
     - a file written with magic 1 is not overwritten with magic 0 (the
       base refuses: "has been modified"), and stays readable;
     - a version not in the list is Bad_version, an unknown magic is
       Bad_magic on read and on write, and a file cut inside its value
       reads as "Failed to find the specified format";
     - pack_version takes a major below 2^15, but refuses a minor or a
       revision of 255, although 255 fits the byte unpack_version reads:
       pinned as found, not changed.
   check's refusal also prints on stderr, naming the temporary file, and
   the runner compares stdout and stderr together, so the test discards
   stderr. *)
open File_base_type
module I = struct
  type select = unit
  type raw = string * int
  type cooked = string
  type arg = unit
  let select = ()
  let suffix = "t"
  let magics = [ 0x111; 0x222 ]
  let versions = [ 5; 4 ]
  let disabled = ref false
  let marshal () c = (c, String.length c)
  let unmarshal () (s, n) = Printf.sprintf "%s/%d" s n
end
module T = struct type select = unit type cooked = string type arg = unit end
module C = File_type_base.MakeSingletonCombo (I)
module FB = File_type_base.MakeFileBase (T) (C)

let root = Filename.concat (Filename.get_temp_dir_name ()) (Printf.sprintf "test_file_type_base_%d" (Unix.getpid ()))
let path = Filename.concat root "m.t"
let header () =
  if not (Sys.file_exists path) then "(none)" else
  let ic = open_in_bin path in
  let r = try let m = input_binary_int ic in let v = input_binary_int ic in Printf.sprintf "magic 0x%x version %d" m v with End_of_file -> "short" in
  close_in ic; r
let raw m v rest = let oc = open_out_bin path in output_binary_int oc m; output_binary_int oc v; output_string oc rest; close_out oc
let attempt what f =
  let r =
    try f () with
    | File_type_base.Bad_magic _ -> "raised Bad_magic"
    | File_type_base.Bad_version (_, vs, v) -> Printf.sprintf "raised Bad_version (wanted [%s], read %d)" (String.concat "; " (List.map string_of_int vs)) v
    | Failure s ->
        (* the messages name the temporary directory: keep the words after the file name (a Unix path, or a
           Windows one, which starts with a drive letter), on the first line only *)
        let first = List.hd (String.split_on_char '\n' s) in
        let words = String.split_on_char ' ' first in
        let rec after = function [] -> [] | w :: r -> if (String.length w > 0 && w.[0] = '/') || (String.length w > 1 && w.[1] = ':') then r else after r in
        "raised Failure: " ^ String.concat " " (match after words with [] -> words | r -> "<file>" :: r)
    | Sys_error s -> "raised Sys_error: " ^ s
    | Invalid_argument s -> "raised Invalid_argument: " ^ s
    | Not_found -> "raised Not_found"
  in
  Printf.printf "%-50s %-40s on disk: %s\n" what r (header ())
let load base () = FB.info base (FB.find_file base () "m" () AnySuffix)
(* check's refusal also prints a line on stderr naming the temporary file,
   and the runner compares stdout and stderr together: discard stderr *)
let () = let null = Unix.openfile Filename.null [ Unix.O_WRONLY ] 0 in Unix.dup2 null Unix.stderr; Unix.close null

let () =
  Unix.mkdir root 0o755;
  let base = FB.create [ root ] in
  let i = FB.create_info base "hello" () root "m" in
  attempt "save" (fun () -> FB.save base () i AnySuffix; "saved");
  attempt "find_file" (load base);
  attempt "set_magic 1, save" (fun () -> FB.set_magic base i 1; FB.save base () i AnySuffix; "saved");
  attempt "find_file" (load base);
  attempt "set_magic 0, save over the magic-1 file" (fun () -> FB.set_magic base i 0; FB.save base () i AnySuffix; "saved");
  attempt "find_file" (load base);
  raw 0x111 9 "";
  attempt "find_file, version 9 on disk" (load base);
  raw 0x999 5 "";
  attempt "find_file, an unknown magic on disk" (load base);
  attempt "save over an unknown magic" (fun () -> FB.save base () i AnySuffix; "saved");
  raw 0x111 5 "\x84\x95";
  attempt "find_file, cut inside the value" (load base);
  Sys.remove path; Unix.rmdir root;
  print_endline "== pack_version";
  let pv a b c = attempt (Printf.sprintf "pack_version %d %d %d" a b c) (fun () ->
      let v = File_type_base.pack_version a b c in
      let x, y, z = File_type_base.unpack_version v in Printf.sprintf "0x%06x -> %d.%d.%d" v x y z) in
  pv 1 2 3; pv 254 254 254; pv 255 0 0; pv 32767 0 0; pv 32768 0 0; pv 0 255 0; pv 0 0 255; pv (-1) 0 0
