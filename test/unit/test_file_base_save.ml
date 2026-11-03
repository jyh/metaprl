(* File_base's write side and its table (test_file_base covers which file
   find loads): none of save, save_as, save_if_newer, save_if_missing,
   create_info, remove_info, clear, find_file, find_match, set_magic was
   entered by a unit test (the 11-02 mllib coverage page). Three suffixes
   a, b, c of one type, as in test_file_base; the marshaller writes the
   content and the magic number, so a file shows which info and which magic
   wrote it. Each step prints what is on disk or what was loaded.
   Recorded rather than modelled: full_name names the first suffix of the
   info's type ("a"), not the file it was loaded from (the info does not
   keep its suffix); set_magic accepts a negative number (its check is only
   "< number of magics"). *)
open File_base_type

module Info = struct
  type select = unit
  type cooked = string
  type arg = unit
  let spec suffix =
    { info_marshal = (fun _ magic _ () name s ->
          let oc = open_out_bin name in Printf.fprintf oc "%s|magic %d" s magic; close_out oc);
      info_unmarshal = (fun _ _ () name ->
          let ic = open_in_bin name in
          let s = really_input_string ic (in_channel_length ic) in
          close_in ic; s, 0);
      info_disabled = ref false;
      info_select = ();
      info_suffix = suffix;
      info_magics = [ 0; 1 ];
      info_versions = [ 0 ] }
  let info = [ spec "a"; spec "b"; spec "c" ]
end

module FB = File_base.MakeFileBase (Info)

let root = Filename.concat (Filename.get_temp_dir_name ()) (Printf.sprintf "test_file_base_save_%d" (Unix.getpid ()))
let d = Filename.concat root "d"
let path sfx = Filename.concat d ("m." ^ sfx)
let disk sfx =
  if Sys.file_exists (path sfx) then
    let ic = open_in_bin (path sfx) in
    let s = really_input_string ic (in_channel_length ic) in close_in ic; Printf.sprintf "%S" s
  else "(none)"
let show what = Printf.printf "%-52s a=%s b=%s c=%s\n" what (disk "a") (disk "b") (disk "c")
let write sfx s time =
  let oc = open_out_bin (path sfx) in output_string oc s; close_out oc; Unix.utimes (path sfx) time time
let attempt what f =
  Printf.printf "%-52s %s\n" what (try f () with e -> "raised " ^ Printexc.to_string e)

let () =
  Unix.mkdir root 0o755; Unix.mkdir d 0o755;
  let base = FB.create [ d ] in
  (* create_info and the save family *)
  let i = FB.create_info base "one" () d "m" in
  show "create_info writes nothing";
  FB.save base () i AnySuffix;
  show "save AnySuffix: the first suffix";
  FB.save base () i (OnlySuffixes [ "c" ]);
  show "save OnlySuffixes [c]";
  FB.set_info base i "two";
  FB.save_if_missing base () i (OnlySuffixes [ "a" ]);
  show "save_if_missing [a], a exists: unchanged";
  FB.save_if_missing base () i (OnlySuffixes [ "b" ]);
  show "save_if_missing [b], b missing: written";
  (* save_if_newer compares the file's mtime with the info's time *)
  Unix.utimes (path "a") 1.0 1.0;
  FB.save_if_newer base () i (OnlySuffixes [ "a" ]);
  show "save_if_newer [a], a older than the info: written";
  Unix.utimes (path "b") 4e9 4e9;
  FB.set_info base i "three";
  FB.save_if_newer base () i (OnlySuffixes [ "b" ]);
  show "save_if_newer [b], b newer than the info: unchanged";
  attempt "create_info again, same dir/file/type" (fun () -> ignore (FB.create_info base "x" () d "m"); "created");
  attempt "save_as, same dir/file/type" (fun () -> ignore (FB.save_as base () "x" () d "m" AnySuffix); "saved");
  (* the table: find returns the cached info, not the disk *)
  attempt "find: the cached info" (fun () -> FB.info base (FB.find base () "m" () AnySuffix));
  attempt "find_match: the cached info" (fun () -> FB.info base (FB.find_match base () i () AnySuffix));
  write "a" "on disk a" 100.; write "b" "on disk b" 50.; write "c" "on disk c" 75.;
  attempt "find_file: the disk (newest is a), not cached" (fun () -> FB.info base (FB.find_file base () "m" () AnySuffix));
  attempt "find after find_file: still the cached info" (fun () -> FB.info base (FB.find base () "m" () AnySuffix));
  FB.remove_info base i;
  attempt "find after remove_info: the disk" (fun () -> FB.info base (FB.find base () "m" () AnySuffix));
  write "c" "on disk c, now newest" 200.;
  attempt "find again: cached from the last load" (fun () -> FB.info base (FB.find base () "m" () AnySuffix));
  FB.clear base;
  let j = FB.find base () "m" () AnySuffix in
  attempt "find after clear: the disk (newest is c)" (fun () -> FB.info base j);
  Printf.printf "%-52s file_name %s, full_name %s\n" "names of the info loaded from m.c"
    (FB.file_name base j) (Filename.basename (FB.full_name base j));
  (* magic *)
  attempt "magic of a loaded info" (fun () -> string_of_int (FB.magic base j));
  attempt "set_magic 1 (two magics)" (fun () -> FB.set_magic base j 1; string_of_int (FB.magic base j));
  FB.save base () j (OnlySuffixes [ "b" ]);
  show "save [b] after set_magic 1";
  attempt "set_magic 2" (fun () -> FB.set_magic base j 2; string_of_int (FB.magic base j));
  attempt "set_magic -1" (fun () -> FB.set_magic base j (-1); string_of_int (FB.magic base j));
  List.iter (fun s -> if Sys.file_exists (path s) then Sys.remove (path s)) [ "a"; "b"; "c" ];
  Unix.rmdir d; Unix.rmdir root
