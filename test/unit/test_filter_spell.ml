(* unit-link: filter *)
(*
 * Filter_spell (filter/base): the dictionary it builds, saves and loads.
 *
 * Filter_spell reads $(MPLIB) when it is loaded and keeps its dictionary
 * in $(MPLIB)/english_dictionary.dat, built from words.metaprl and
 * words.linux beside it.  So that no case writes into the tree's own lib,
 * each case is a child process (this program again) whose MPLIB is a
 * fresh directory that this process sets up; the child prints what
 * Filter_spell.check answers.  The tree's own dictionary is read only
 * for its modification time, before and after.
 *
 * The cases: a first build (no .dat), a load of an up-to-date .dat, a
 * rebuild when a words file is newer than the .dat, a rebuild when the
 * .dat's magic number is wrong, a rebuild when its magic is right but
 * its table cannot be read, and a build with no words files at all.
 * A load is told from a rebuild by a word added to a words file without
 * moving its modification time forward: a load does not see it.
 *
 * On a bisect build at 008a9607e the theory build and the proof census
 * reach none of the dictionary's build, load or staleness code: the
 * tree's .dat is already there.
 *
 * The expected file is the output of the code.
 *)

let dat = "english_dictionary.dat"
let magic = 0x2557f3ef

let words = [
   "alpha"; "Alpha"; "ALPHA"; "beta"; "gamma"; "delta"; "world";
   "zzz"; "Zzz"; "a"; "Q"; ""; "42"; "4x"; "x4"; "007"
]

let child phase =
   Printf.printf "%s:\n" phase;
   Printf.printf "  before init: zzz %b\n" (Filter_spell.check "zzz");
   Filter_spell.init ();
   let yes, no = List.partition Filter_spell.check words in
   let show l = String.concat " " (List.map (Printf.sprintf "%S") l) in
      Printf.printf "  spelled: %s\n  not:     %s\n" (show yes) (show no);
   Filter_spell.add "zzz";
   Printf.printf "  after add zzz: zzz %b\n" (Filter_spell.check "zzz");
   Filter_spell.init ();
   Printf.printf "  after a second init: zzz %b\n" (Filter_spell.check "zzz")

(*
 * The parent's side.
 *)
let counter = ref 0

let fresh_dir () =
   incr counter;
   let name =
      Printf.sprintf "test_filter_spell_%d_%d" (Unix.getpid ()) !counter
   in
   let dir = Filename.concat (Filename.get_temp_dir_name ()) name in
      Unix.mkdir dir 0o700;
      dir

let write_file file text =
   let out = open_out_bin file in
      output_string out text;
      close_out out

let set_mtime file t =
   Unix.utimes file t t

let run dir phase =
   flush stdout;
   let env =
      Array.append
         [| "MPLIB=" ^ dir; "TEST_FILTER_SPELL=" ^ phase |]
         (Array.of_list
            (List.filter (fun s ->
                 not (String.length s >= 6 && String.sub s 0 6 = "MPLIB=")
                 && not (String.length s >= 18 && String.sub s 0 18 = "TEST_FILTER_SPELL="))
               (Array.to_list (Unix.environment ()))))
   in
   let pid =
      Unix.create_process_env Sys.executable_name [| Sys.executable_name |] env
         Unix.stdin Unix.stdout Unix.stderr
   in
      match Unix.waitpid [] pid with
         _, Unix.WEXITED 0 -> ()
       | _, Unix.WEXITED n -> Printf.printf "  child exited %d\n" n
       | _ -> Printf.printf "  child killed\n"

(* What is in the directory, besides the words files. *)
let report dir =
   let files = Array.to_list (Sys.readdir dir) in
   let files = List.sort compare (List.filter (fun f -> f <> "words.metaprl" && f <> "words.linux") files) in
   let others = List.filter (fun f -> f <> dat) files in
      Printf.printf "  files: .dat %b, others %d\n" (List.mem dat files) (List.length others);
      if List.mem dat files then begin
         let inx = open_in_bin (Filename.concat dir dat) in
         let m = input_binary_int inx in
            close_in inx;
            Printf.printf "  .dat magic ok: %b\n" (m = magic)
      end

let remove_dir dir =
   Array.iter (fun f -> Sys.remove (Filename.concat dir f)) (Sys.readdir dir);
   Unix.rmdir dir

let mtime file =
   try Some (Unix.stat file).Unix.st_mtime with Unix.Unix_error _ -> None

let parent () =
   let own = Filename.concat (Sys.getenv "MPLIB") dat in
   let own_before = mtime own in
   let now = Unix.time () in
   let old = now -. 2000. in
   let dir = fresh_dir () in
   let metaprl = Filename.concat dir "words.metaprl" in
   let linux = Filename.concat dir "words.linux" in
   let datf = Filename.concat dir dat in
      write_file metaprl "alpha\nbeta\n";
      write_file linux "world\n";

      (* 1. No .dat: built from both words files. *)
      run dir "first build";
      report dir;

      (* 2. Both words files older than the .dat: loaded, so gamma,
       *    added to words.metaprl without moving its time, is not seen. *)
      write_file metaprl "alpha\nbeta\ngamma\n";
      set_mtime metaprl old;
      set_mtime linux old;
      set_mtime datf (old +. 1000.);
      run dir "up-to-date .dat";

      (* 3. words.linux newer than the .dat: rebuilt, gamma is seen. *)
      set_mtime linux (old +. 1500.);
      run dir "words.linux newer than the .dat";
      report dir;

      (* 4. Wrong magic, words older: rebuilt (delta is seen). *)
      write_file metaprl "alpha\nbeta\ngamma\ndelta\n";
      set_mtime metaprl old;
      set_mtime linux old;
      write_file datf "\000\000\000\001garbage";
      set_mtime datf (old +. 1000.);
      run dir "wrong magic";
      report dir;

      (* 5. Right magic, unreadable table, words older: rebuilt. *)
      write_file metaprl "alpha\n";
      set_mtime metaprl old;
      (let out = open_out_bin datf in
          output_binary_int out magic;
          output_string out "not a marshalled table";
          close_out out);
      set_mtime datf (old +. 1000.);
      run dir "right magic, unreadable table";
      report dir;

      (* 6. No words files at all: an empty dictionary. *)
      let empty = fresh_dir () in
         run empty "no words files";
         report empty;
         remove_dir empty;
         remove_dir dir;

      Printf.printf "the tree's own .dat unchanged: %b\n" (mtime own = own_before)

let () =
   match Sys.getenv_opt "TEST_FILTER_SPELL" with
      Some phase -> child phase
    | None -> parent ()
