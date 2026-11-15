(* Http_simple's serving loop when its listening socket is closed (row 624):
   serve retries a failed accept for ever (accept's Unix_error -> None ->
   serve info), so a server whose socket is gone spins, logging "accept
   failed" each time, and never returns.  test_http_serve met it as a side
   effect on macOS, where closing the socket wakes the threads blocked in
   accept; on Linux close does not wake them, so that shape is not portable.
   This one is: the start handler calls close_http on the socket BEFORE
   serve_http starts serving (and before it creates its other threads), so
   every accept is on a closed socket, on every platform.
   The test runs itself again as a child that serves that way, reads the
   child's stderr for up to 3 s, counts the "accept failed" lines, and kills
   the child.  Pinned as found: the loop spins (at least 5 such lines, the
   child still running).  The expected file is the output of the code as
   written, never typed. *)

let child () =
  let start t info = Http_simple.close_http t; info in
  let connect _ info _ _ _ _ _ = info in
  Http_simple.serve_http start connect () 0

let parent () =
  let r, w = Unix.pipe () in
  let pid = Unix.create_process Sys.executable_name [| Sys.executable_name; "child" |] Unix.stdin Unix.stdout w in
  Unix.close w;
  (* A reader thread, not select: select does not take a pipe on Windows. *)
  let m = Mutex.create () and buf = Buffer.create 4096 and eof = ref false in
  let reader () =
    let chunk = Bytes.create 4096 in
    let rec loop () =
      let n = try Unix.read r chunk 0 4096 with Unix.Unix_error _ -> 0 in
      Mutex.lock m;
      if n > 0 then Buffer.add_subbytes buf chunk 0 n else eof := true;
      Mutex.unlock m;
      if n > 0 then loop ()
    in
    loop ()
  in
  let th = Thread.create reader () in
  let has k l = let n = String.length l and m = String.length k in
    let rec at i = i + m <= n && (String.sub l i m = k || at (i + 1)) in at 0 in
  let count () =
    Mutex.lock m;
    let c = List.length (List.filter (has "accept failed") (String.split_on_char '\n' (Buffer.contents buf))) and e = !eof in
    Mutex.unlock m; c, e in
  let deadline = Unix.gettimeofday () +. 3.0 in
  let rec wait () =
    let c, e = count () in
    if c < 5 && not e && Unix.gettimeofday () < deadline then (Thread.delay 0.05; wait ()) in
  wait ();
  let c, exited = count () in
  (try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ());
  ignore (try Unix.waitpid [] pid with Unix.Unix_error _ -> (pid, Unix.WEXITED 0));
  Thread.join th;
  Unix.close r;
  Printf.printf "accept failed logged at least 5 times: %b\n" (c >= 5);
  Printf.printf "the child still running after them: %b\n" (not exited)

let () = if Array.length Sys.argv > 1 && Sys.argv.(1) = "child" then child () else parent ()
