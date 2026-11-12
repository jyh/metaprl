(* File_base (mllib) when one format has several specs: load picks the
   spec whose file is newest (newest_spec), and a spec whose file is
   missing counts as time 0.  The census reaches this through the
   theory formats; no unit test had more than one enabled spec per
   format.  A base over three specs of format A, each reading a file's
   whole contents:
     A ".x1"      A ".x2"      A ".x3"
   For each case a fresh base is made over a fresh directory holding
   the listed files with the given modification times; the line prints
   the suffix whose file was loaded (each file's contents is its own
   suffix) or the refusal.  The comparison is strict, so on a tie the
   earlier spec is kept.  A refusal's message names the temporary
   directory, so only its first line is printed. *)
type select = A

module Info = struct
  type nonrec select = select
  type cooked = string
  type arg = unit
  let read f = let ic = open_in_bin f in let n = in_channel_length ic in let s = really_input_string ic n in close_in ic; s
  let spec suffix = {
    File_base_type.info_marshal = (fun _ _ _ () f s -> let oc = open_out_bin f in output_string oc s; close_out oc);
    info_unmarshal = (fun _ _ () f -> read f, 0);
    info_disabled = ref false; info_select = A; info_suffix = suffix; info_magics = [ 0 ]; info_versions = [ 0 ] }
  let info = [ spec "x1"; spec "x2"; spec "x3" ]
end
module FB = File_base.MakeFileBase (Info)

let dir = Filename.concat (Filename.get_temp_dir_name ()) (Printf.sprintf "test_file_base_newest_%d" (Unix.getpid ()))
let suffixes = [ "x1"; "x2"; "x3" ]
let clear () = List.iter (fun s -> let f = Filename.concat dir ("m." ^ s) in if Sys.file_exists f then Sys.remove f) suffixes

let case name files suffix =
  clear ();
  List.iter (fun (s, t) ->
      let f = Filename.concat dir ("m." ^ s) in
      let oc = open_out_bin f in output_string oc s; close_out oc; Unix.utimes f t t) files;
  let r =
    try let base = FB.create [ dir ] in FB.info base (FB.find base () "m" A suffix) with
      Failure s -> "Failure: " ^ List.hd (String.split_on_char '\n' s)
  in
  Printf.printf "%-40s %s\n" name r

let () =
  Unix.mkdir dir 0o755;
  let any = File_base_type.AnySuffix in
  case "only x2" [ "x2", 100. ] any;
  case "only x3" [ "x3", 100. ] any;
  case "only x1" [ "x1", 100. ] any;
  case "x1 100, x2 300, x3 200" [ "x1", 100.; "x2", 300.; "x3", 200. ] any;
  case "x1 300, x2 100, x3 200" [ "x1", 300.; "x2", 100.; "x3", 200. ] any;
  case "x1 100, x2 200, x3 300" [ "x1", 100.; "x2", 200.; "x3", 300. ] any;
  case "x1 100, x3 200 (x2 missing)" [ "x1", 100.; "x3", 200. ] any;
  case "x2 200, x3 100 (x1 missing)" [ "x2", 200.; "x3", 100. ] any;
  case "all 100 (tie)" [ "x1", 100.; "x2", 100.; "x3", 100. ] any;
  case "x1 100, x2 200, x3 200 (tie)" [ "x1", 100.; "x2", 200.; "x3", 200. ] any;
  case "x1 300, x2 100, x3 200, only x2/x3" [ "x1", 300.; "x2", 100.; "x3", 200. ] (File_base_type.OnlySuffixes [ "x2"; "x3" ]);
  case "x1 300, only x2/x3 (neither exists)" [ "x1", 300. ] (File_base_type.OnlySuffixes [ "x2"; "x3" ]);
  case "none" [] any;
  clear ();
  Unix.rmdir dir
