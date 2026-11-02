(* Setup (mllib): where MetaPRL finds its tree and keeps its state —
   MP_ROOT, MPLIB (or $MP_ROOT/lib), doc_dir, $HOME/.metaprl, the editor,
   the browser hostname (and, through home, the unexported ensure_dir). Every value is computed
   once per process from the environment, so each case is a child process
   (this executable again) whose HOME and MP_ROOT point into a temporary
   directory; nothing outside it is read or written. Paths print with that
   directory as <T> and "/" as the separator. Not covered: HOME unset (it
   falls back to /tmp/metaprl-<uid>, outside the temporary directory), and
   the certificate files (with SSL enabled they run openssl; whether a build
   enables SSL differs between machines, so their output would too). *)

let t = Filename.concat (Filename.get_temp_dir_name ()) (Printf.sprintf "test_setup_%d" (Unix.getpid ()))

let show s =
  let s = String.map (fun c -> if c = '\\' then '/' else c) s in
  let p = String.map (fun c -> if c = '\\' then '/' else c) (Sys.getenv "TEST_SETUP_T") in
  let n = String.length p in
  let rec go i acc =
    if i >= String.length s then String.concat "" (List.rev acc)
    else if i + n <= String.length s && String.sub s i n = p then go (i + n) ("<T>" :: acc)
    else go (i + 1) (String.make 1 s.[i] :: acc) in
  go 0 []

let attempt name f =
  Printf.printf "  %s: %s\n%!" name
    (try f () with Invalid_argument m -> "Invalid_argument " ^ m | Failure m -> "Failure " ^ m)

let child case =
  match case with
  | "paths" ->
      attempt "root" Setup.root;
      attempt "lib" Setup.lib;
      attempt "doc_dir" (fun () -> match Setup.doc_dir () with Some d -> "Some " ^ d | None -> "None")
  | "home" ->
      attempt "home (first call)" Setup.home;
      attempt "home (second call)" Setup.home;
      attempt ".metaprl is a directory" (fun () ->
          string_of_bool (Sys.is_directory (Filename.concat (Sys.getenv "HOME") ".metaprl")))
  | "editor" -> attempt "editor" Setup.editor
  | "hostname" ->
      attempt "gethostname" Setup.gethostname;
      Setup.sethostname "other.example";
      attempt "after sethostname: gethostname" Setup.gethostname;
      attempt "after sethostname: MP_BROWSER_HOSTNAME" (fun () -> Sys.getenv "MP_BROWSER_HOSTNAME")
  | c -> Printf.printf "unknown case %s\n" c

let rec rm_rf p =
  if Sys.file_exists p then
    if Sys.is_directory p then begin
      Array.iter (fun e -> rm_rf (Filename.concat p e)) (Sys.readdir p); Unix.rmdir p
    end else Sys.remove p

let mkdirs l = List.iter (fun d -> Unix.mkdir (Filename.concat t d) 0o755) l

let run name case env setup =
  rm_rf t; Unix.mkdir t 0o755; setup ();
  let keep e = not (List.exists (fun p -> String.length e >= String.length p && String.sub e 0 (String.length p) = p)
                      [ "HOME="; "MP_"; "MPLIB="; "EDITOR="; "TEST_SETUP_" ]) in
  let env = Array.of_list (("TEST_SETUP_T=" ^ t) :: env @ List.filter keep (Array.to_list (Unix.environment ()))) in
  let r, w = Unix.pipe () in
  let pid = Unix.create_process_env Sys.executable_name [| Sys.executable_name; "--child"; case |] env Unix.stdin w w in
  Unix.close w;
  let ic = Unix.in_channel_of_descr r in
  let rec lines acc = match input_line ic with l -> lines (String.trim l :: acc) | exception End_of_file -> List.rev acc in
  let out = lines [] in
  close_in ic;
  let st = match snd (Unix.waitpid [] pid) with Unix.WEXITED n -> Printf.sprintf "exit %d" n | _ -> "killed" in
  Printf.printf "%s (%s)\n" name st;
  Unix.putenv "TEST_SETUP_T" t;
  List.iter (fun l -> if l <> "" then Printf.printf "    %s\n" (show l)) out

let () =
  if Array.length Sys.argv > 2 && Sys.argv.(1) = "--child" then child Sys.argv.(2)
  else begin
    let at d = Filename.concat t d in
    run "MP_ROOT unset" "paths" [] (fun () -> ());
    run "MP_ROOT with lib/ and doc/htmlman/" "paths" [ "MP_ROOT=" ^ at "root" ] (fun () ->
        mkdirs [ "root"; "root/lib"; "root/doc"; "root/doc/htmlman" ]);
    run "MP_ROOT with no lib/, no doc/" "paths" [ "MP_ROOT=" ^ at "root" ] (fun () -> mkdirs [ "root" ]);
    run "MPLIB set (wins over MP_ROOT/lib)" "paths" [ "MP_ROOT=" ^ at "root"; "MPLIB=" ^ at "mylib" ] (fun () ->
        mkdirs [ "root"; "root/lib" ]);
    run "HOME without .metaprl" "home" [ "HOME=" ^ at "h" ] (fun () -> mkdirs [ "h" ]);
    run "HOME with .metaprl" "home" [ "HOME=" ^ at "h" ] (fun () -> mkdirs [ "h"; "h/.metaprl" ]);
    run "editor: no file, EDITOR=ed" "editor" [ "HOME=" ^ at "h"; "EDITOR=ed" ] (fun () -> mkdirs [ "h"; "h/.metaprl" ]);
    run "editor: no file, no EDITOR" "editor" [ "HOME=" ^ at "h" ] (fun () -> mkdirs [ "h"; "h/.metaprl" ]);
    run "editor: .metaprl/editor holds emacs" "editor" [ "HOME=" ^ at "h"; "EDITOR=ed" ] (fun () ->
        mkdirs [ "h"; "h/.metaprl" ];
        let oc = open_out (at "h/.metaprl/editor") in output_string oc "emacs -nw\nsecond line\n"; close_out oc);
    run "hostname from MP_BROWSER_HOSTNAME" "hostname" [ "HOME=" ^ at "h"; "MP_BROWSER_HOSTNAME=test.example" ]
      (fun () -> mkdirs [ "h" ]);
    run "HOME/.metaprl is a plain file" "home" [ "HOME=" ^ at "h" ] (fun () ->
        mkdirs [ "h" ]; close_out (open_out (at "h/.metaprl")));
    rm_rf t
  end
