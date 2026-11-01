(* File_base (mllib) loads a module from the first directory on its path
   that has one of the module's files, choosing among the file types (here
   three suffixes a, b, c, in that order) the file with the NEWEST mtime;
   a missing file counts as time 0, and on equal times the earlier suffix
   wins.  The theory archives (.cmoz, .prlb, .prla) are chosen this way, so
   a newer archive of any kind shadows the others: a session's auto-saved
   .cmoz is read instead of the stored .prla.
   Each case writes files whose content names their directory and suffix,
   sets their mtimes, and compares what File_base.find loads with a model
   of that rule.  One case has no model and is recorded: the newest file
   is corrupt (its unmarshal raises).  Not covered: an unreadable newest
   file (permissions differ on Windows and under root). *)
open File_base_type

module Info = struct
  type select = unit
  type cooked = string
  type arg = unit
  let spec suffix =
    { info_marshal = (fun _ _ _ () name s ->
          let oc = open_out_bin name in output_string oc s; close_out oc);
      info_unmarshal = (fun _ _ () name ->
          let ic = open_in_bin name in
          let s = really_input_string ic (in_channel_length ic) in
          close_in ic;
          if s = "corrupt" then failwith ("cannot unmarshal " ^ Filename.basename name);
          s, 0);
      info_disabled = ref false;
      info_select = ();
      info_suffix = suffix;
      info_magics = [ 0 ];
      info_versions = [ 0 ] }
  let info = [ spec "a"; spec "b"; spec "c" ]
end

module FB = File_base.MakeFileBase (Info)

let root = Filename.concat (Filename.get_temp_dir_name ()) (Printf.sprintf "test_file_base_%d" (Unix.getpid ()))
let n = ref 0
let made = ref []

(* A case: two directories; each file is (dir, suffix, mtime, content). *)
let case name files =
  incr n;
  let d k = Filename.concat root (Printf.sprintf "c%d_d%d" !n k) in
  List.iter (fun k -> Unix.mkdir (d k) 0o755; made := `Dir (d k) :: !made) [ 1; 2 ];
  List.iter (fun (k, sfx, time, content) ->
      let f = Filename.concat (d k) ("m." ^ sfx) in
      let oc = open_out_bin f in
      output_string oc (match content with Some c -> c | None -> Printf.sprintf "d%d/%s" k sfx);
      close_out oc;
      made := `File f :: !made;
      Unix.utimes f time time) files;
  (* the model: the first directory with any file; in it the newest, the
     earlier suffix on a tie *)
  let model =
    let in_dir k = List.filter (fun (k', _, _, _) -> k' = k) files in
    match List.find_opt (fun k -> in_dir k <> []) [ 1; 2 ] with
    | None -> "Failure"
    | Some k ->
        let time sfx = match List.find_opt (fun (_, s, _, _) -> s = sfx) (in_dir k) with
          | Some (_, _, t, _) -> t | None -> 0.0 in
        let best = List.fold_left (fun b s -> if time s > time b then s else b) "a" [ "b"; "c" ] in
        Printf.sprintf "d%d/%s" k best
  in
  let base = FB.create [ d 1; d 2 ] in
  let got =
    try FB.info base (FB.find base () "m" () AnySuffix) with
    | Failure s when String.length s >= 9 && String.sub s 0 9 = "Failed to" -> "Failure"
    | e -> "raised " ^ Printexc.to_string e
  in
  let has_model = not (List.exists (fun (_, _, _, c) -> c <> None) files) in
  Printf.printf "%-48s loads %-38s %s\n" name got
    (if not has_model then "(recorded)" else if got = model then "= model" else "DIFFERS from model " ^ model)

let () =
  Unix.mkdir root 0o755;
  case "only b" [ 1, "b", 100., None ];
  case "a b c at 100 300 200" [ 1, "a", 100., None; 1, "b", 300., None; 1, "c", 200., None ];
  case "a b c all at 200 (a tie)" [ 1, "a", 200., None; 1, "b", 200., None; 1, "c", 200., None ];
  case "b c tie at 200, a older" [ 1, "a", 100., None; 1, "b", 200., None; 1, "c", 200., None ];
  case "c newest" [ 1, "a", 100., None; 1, "b", 200., None; 1, "c", 300., None ];
  case "dir 1 has old c, dir 2 has newer a" [ 1, "c", 10., None; 2, "a", 999., None ];
  case "dir 1 empty, dir 2 has b" [ 2, "b", 100., None ];
  case "no file anywhere" [];
  case "newest (c) corrupt, older a fine" [ 1, "a", 100., None; 1, "c", 300., Some "corrupt" ];
  List.iter (function `File f -> Sys.remove f | `Dir _ -> ()) !made;
  List.iter (function `Dir d -> Unix.rmdir d | `File _ -> ()) !made;
  Unix.rmdir root
