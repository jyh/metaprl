(* Http_simple.serve_http, the browser shell's web server, end to end over
   loopback: untested until now. The server runs in a thread on port 0; its
   start handler reports the real port (http_info). Each request is a fresh
   connection, as the server shuts down and closes after every reply, and the
   client reads to end of file. Printed: the status line and the body (the
   headers carry a date). Cases: a GET whose path the handler decodes with
   decode_uri; a POST with a form-urlencoded body; a path with a malformed
   escape, which raises Failure in the handler: the serving loop catches it for
   that request (no reply; it logs "error during web service") and goes on. The
   log line is the evidence: serve_http runs several serving threads, so "the
   next request is still served" would hold even if one thread died (a mutant
   that lets Failure escape logs "service closed" and "Uncaught thread exception"
   instead, and the next request is still answered by another thread). The log
   line for that request precedes "bad escape" by construction: it is written
   before the server closes the connection, and the client prints only after
   end of file. A client read times out after 10 s, so a server that stops
   serving reads as "(no reply)" instead of hanging the suite. *)
open Http_server_type

let port = ref 0
let m = Mutex.create ()
let c = Condition.create ()

let start t info =
  let i = Http_simple.http_info t in
  Mutex.lock m; port := i.http_port; Condition.signal c; Mutex.unlock m;
  info

let connect _t info out _inx args header body =
  let buf = Buffer.create 64 in
  (match args with
   | meth :: uri :: _ ->
       Buffer.add_string buf (meth ^ " " ^ String.concat "|" (Http_simple.decode_uri uri));
       if meth = "post" then begin
         match List.find_map (function RequestContentType ct -> Some ct | _ -> None) header with
         | Some ct ->
             List.iter (fun (k, v) -> Buffer.add_string buf (Printf.sprintf " %s=%s" k v))
               (Http_simple.parse_post_body ct body)
         | None -> Buffer.add_string buf " (no content type)"
       end
   | _ -> Buffer.add_string buf "no request line");
  Http_simple.print_success_page out OkCode buf;
  info

let request text =
  let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  (* A server that stopped serving leaves the connection unanswered: time out
     rather than hang the suite. *)
  Unix.setsockopt_float s Unix.SO_RCVTIMEO 10.0;
  Unix.connect s (Unix.ADDR_INET (Unix.inet_addr_loopback, !port));
  ignore (Unix.write_substring s text 0 (String.length text));
  let b = Buffer.create 256 and chunk = Bytes.create 256 in
  let rec loop () =
    let n = try Unix.read s chunk 0 256 with Unix.Unix_error _ -> 0 in
    if n > 0 then (Buffer.add_subbytes b chunk 0 n; loop ())
  in
  loop ();
  Unix.close s;
  let r = Buffer.contents b in
  let lines = String.split_on_char '\n' r |> List.map (fun l -> String.trim l) in
  match lines with
  | [] | [ "" ] -> "(no reply)"
  | status :: rest ->
      let rec body = function "" :: tl -> String.concat "/" (List.filter (( <> ) "") tl) | _ :: tl -> body tl | [] -> "" in
      status ^ " :: " ^ body rest

let () =
  ignore (Lm_thread.Thread.create (fun () -> Http_simple.serve_http start connect () 0) ());
  Mutex.lock m;
  while !port = 0 do Condition.wait c m done;
  Mutex.unlock m;
  print_endline (if !port > 0 then "server bound to a port" else "no port");
  List.iter (fun (name, text) -> Printf.printf "%s: %s\n%!" name (request text))
    [ ("GET", "GET /a%20b/c/../d HTTP/1.0\r\n\r\n");
      ("POST", "POST /form HTTP/1.0\r\nContent-Type: application/x-www-form-urlencoded\r\nContent-Length: 12\r\n\r\nx=1&y=a+b%26");
      ("bad escape", "GET /%zz HTTP/1.0\r\n\r\n");
      ("after it", "GET /still/up HTTP/1.0\r\n\r\n") ];
  exit 0
