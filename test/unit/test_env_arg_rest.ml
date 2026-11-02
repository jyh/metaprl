(* Env_arg's other half (test_env_arg has the string/int/bool options and
   their precedence): the option-valued setters, putenv, MP_DEBUG and -debug,
   parse and usage. None was entered by a unit test (the 11-02 mllib coverage
   page). As in test_env_arg, each case is a child process (this executable
   again), because options read the environment when they are created and a
   bad -debug exits. Cases:
   - string and int options whose cell is an option (default None): neither,
     the environment, the command line (through Env_arg.parse, so it is
     driven too);
   - putenv "tput" sets MP_TPUT, and an option created after it reads it;
   - MP_DEBUG names a debug flag that is created only later (Env_arg reads
     MP_DEBUG when it loads, before the test's own module creates the flag),
     so it must be remembered and applied at creation; and -debug on the
     command line; two names separated by ":";
   - -debug with an unknown name: usage on stderr, exit 1;
   - usage: the test's own extra option and the -t options it created.
   Usage also lists every debug flag of every linked library, so the parent
   keeps only the lines naming this test's own options and flags, and the
   header lines, and notes that others were dropped (their number moves with
   every flag a library adds). *)

let child case =
  let sopt = Env_arg.string "topt" None "an optional string" Env_arg.set_string_option_string in
  let iopt = Env_arg.int "tiopt" None "an optional int" Env_arg.set_int_option_int in
  let d1 = Lm_debug.create_debug { Lm_debug.debug_name = "tdbg_one"; debug_description = "test flag one"; debug_value = false } in
  let d2 = Lm_debug.create_debug { Lm_debug.debug_name = "tdbg_two"; debug_description = "test flag two"; debug_value = false } in
  let extra = [ ("-textra", Arg.Unit (fun () -> print_endline "textra given"), ": an extra option") ] in
  let show () =
    let so = match !sopt with None -> "None" | Some s -> Printf.sprintf "Some %S" s in
    let io = match !iopt with None -> "None" | Some i -> Printf.sprintf "Some %d" i in
    Printf.printf "topt=%s tiopt=%s tdbg_one=%b tdbg_two=%b\n%!" so io !d1 !d2 in
  match case with
  | "parse" ->
      (* argv is: exe --child parse <args>; Arg.parse starts after !Arg.current. *)
      Arg.current := 2;
      Env_arg.parse extra (fun a -> Printf.printf "anonymous %s\n" a) "usage message";
      show ()
  | "putenv" ->
      Env_arg.putenv "tput" "from putenv";
      let p = Env_arg.string "tput" "default" "set by putenv" Env_arg.set_string_string in
      Printf.printf "MP_TPUT=%S tput=%S\n" (Sys.getenv "MP_TPUT") !p
  | "usage" -> Env_arg.usage extra "usage message"; prerr_string ""
  | c -> Printf.printf "unknown case %s\n" c

let cases = [
  "options: neither", [], [ "parse" ];
  "options: environment", [ "MP_TOPT=env"; "MP_TIOPT=5" ], [ "parse" ];
  "options: command line", [], [ "parse"; "-topt"; "cmd"; "-tiopt"; "9"; "-textra"; "anon" ];
  "MP_DEBUG before the flag exists", [ "MP_DEBUG=tdbg_two" ], [ "parse" ];
  "MP_DEBUG two names", [ "MP_DEBUG=tdbg_one:tdbg_two" ], [ "parse" ];
  "-debug on the command line", [], [ "parse"; "-debug"; "tdbg_one" ];
  "-debug unknown name", [], [ "parse"; "-debug"; "no_such_flag" ];
  "putenv", [], [ "putenv" ];
  "usage", [], [ "usage" ];
]

(* Usage text: keep the header lines and this test's own names; count the rest. *)
let keep l =
  let has s = let n = String.length s and m = String.length l in
    let rec go i = i + n <= m && (String.sub l i n = s || go (i + 1)) in go 0 in
  List.exists has [ "-topt"; "-tiopt"; "-textra"; "-debug"; "tdbg_"; "usage message"; "illegal option";
                    "Debugging flags"; "colon-separated"; "topt="; "MP_TPUT"; "anonymous"; "textra given";
                    "unknown case" ]

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
  Printf.printf "%-34s %s\n" name status;
  let kept = List.filter keep out in
  List.iter (Printf.printf "    %s\n") kept;
  let other = List.length out - List.length kept in
  if other > 0 then print_endline "    (and other lines)"

let () =
  if Array.length Sys.argv > 2 && Sys.argv.(1) = "--child" then child Sys.argv.(2)
  else List.iter run cases
