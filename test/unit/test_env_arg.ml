(* Env_arg (mllib): options that come from MP_<NAME> in the environment or
   -<name> on the command line, used by 11 modules (the shell, the editor,
   the refiner's debug flags).  Each case runs in a child process (this
   executable again, with the case's environment and arguments), since an
   option reads the environment when it is created and a bad value exits;
   the parent prints each child's output and exit status.  Cases:
   string / int / bool options from neither, the environment, the command
   line, and both (the command line wins); a bad int and a bad bool in the
   environment; the option names Env_arg.args lists.  Until it was fixed,
   a bad int printed "'int_of_string' not integer", not the value: the
   handler's `Failure s` shadowed the string it reports. *)
let child () =
  let s = Env_arg.string "tstr" "default" "a string" Env_arg.set_string_string in
  let i = Env_arg.int "tint" 7 "an int" Env_arg.set_int_int in
  let b = Env_arg.bool "tbool" false "a bool" Env_arg.set_bool_bool in
  let names = List.sort compare (List.filter (fun n -> String.length n > 2 && String.sub n 0 2 = "-t")
      (List.map (fun (k, _, _) -> k) (Env_arg.args ()))) in
  let argv = Array.of_list ("child" :: List.tl (List.tl (Array.to_list Sys.argv))) in
  (try Arg.parse_argv ~current:(ref 0) argv (Env_arg.args ()) (fun _ -> ()) "usage"
   with Arg.Bad m | Arg.Help m -> Printf.printf "Arg: %s\n" (List.hd (String.split_on_char '\n' m)));
  Printf.printf "tstr=%S tint=%d tbool=%b args=%s\n" !s !i !b (String.concat "," names)

let cases = [
  "neither", [], [];
  "environment", [ "MP_TSTR=env"; "MP_TINT=12"; "MP_TBOOL=true" ], [];
  "command line", [], [ "-tstr"; "cmd"; "-tint"; "34"; "-tbool" ];
  "both (command line wins)", [ "MP_TSTR=env"; "MP_TINT=12" ], [ "-tstr"; "cmd"; "-tint"; "34" ];
  "bad int in the environment", [ "MP_TINT=x12" ], [];
  "bad bool in the environment", [ "MP_TBOOL=yes" ], [];
]

let run (name, env, args) =
  let env = Array.append (Array.of_list env)
      (Array.of_list (List.filter (fun e -> not (String.length e > 3 && String.sub e 0 3 = "MP_")) (Array.to_list (Unix.environment ())))) in
  let out_r, out_w = Unix.pipe () in
  let pid = Unix.create_process_env Sys.executable_name
      (Array.of_list (Sys.executable_name :: "--child" :: args)) env Unix.stdin out_w out_w in
  Unix.close out_w;
  let ic = Unix.in_channel_of_descr out_r in
  let rec lines acc = match input_line ic with l -> lines (String.trim l :: acc) | exception End_of_file -> List.rev acc in
  let out = lines [] in
  close_in ic;
  let status = match snd (Unix.waitpid [] pid) with
    | Unix.WEXITED n -> Printf.sprintf "exit %d" n
    | Unix.WSIGNALED n -> Printf.sprintf "signal %d" n
    | Unix.WSTOPPED n -> Printf.sprintf "stopped %d" n in
  Printf.printf "%-28s %s\n" name status;
  List.iter (Printf.printf "    %s\n") out

let () =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "--child" then child ()
  else List.iter run cases
