(* Http_simple's response printers, over loopback: none was entered by any
   unit test (the 11-02 mllib coverage page). The server runs as in
   test_http_serve (a thread, port 0, one connection per request, HTTP/1.0 so
   it closes after each reply); the handler picks a printer by the request's
   first path component. The client prints the reply's header lines verbatim,
   with "\r" shown, so a missing CR or a wrong blank line shows, and then
   whether Content-Length equals the body's byte count. The served file for
   the channel printers has its modification time set to 1000000000.0, so
   Last-Modified is fixed. Cases: every response code through
   print_success_header (its status line is the whole of get_code); one page,
   one content page, one error page, one redirect, the file through both
   channel printers. Not covered: the channel printers' no-fstat branch
   (Win32, by its comment), and SigPipe (a client that hangs up). *)
open Http_server_type

let port = ref 0
let m = Mutex.create ()
let c = Condition.create ()
let file = "test_http_print.tmp"

let codes =
  [| ContinueCode; OkCode; CreatedCode; AcceptedCode; NoContentCode; MovedPermCode; MovedTempCode; SeeOtherCode;
     NotModifiedCode; BadRequestCode; UnauthorizedCode; ForbiddenCode; NotFoundCode; ServerErrorCode;
     NotImplementedCode; BadGatewayCode; ServiceUnavailableCode |]

let start t info =
  let i = Http_simple.http_info t in
  Mutex.lock m; port := i.http_port; Condition.signal c; Mutex.unlock m;
  info

let connect _t info out _inx args _header _body =
  let path = match args with _ :: uri :: _ -> Http_simple.decode_uri uri | _ -> [] in
  let buf = Buffer.create 16 in
  Buffer.add_string buf "a body\n";
  (match path with
   | [ "code"; n ] -> Http_simple.print_success_header out codes.(int_of_string n)
   | [ "page" ] -> Http_simple.print_success_page out OkCode buf
   | [ "content" ] -> Http_simple.print_content_page out CreatedCode "text/plain" buf
   | [ "error" ] -> Http_simple.print_error_page out NotFoundCode
   | [ "redirect" ] -> Http_simple.print_redirect_page out MovedTempCode "/else/where"
   | [ "channel" ] ->
       let ic = open_in_bin file in Http_simple.print_success_channel out OkCode ic; close_in ic
   | [ "cchannel" ] ->
       let ic = open_in_bin file in Http_simple.print_content_channel out OkCode "text/html" ic; close_in ic
   | _ -> Http_simple.print_error_page out BadRequestCode);
  info

let request path =
  let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  Unix.setsockopt_float s Unix.SO_RCVTIMEO 10.0;
  Unix.connect s (Unix.ADDR_INET (Unix.inet_addr_loopback, !port));
  let text = "GET " ^ path ^ " HTTP/1.0\r\n\r\n" in
  ignore (Unix.write_substring s text 0 (String.length text));
  let b = Buffer.create 256 and chunk = Bytes.create 256 in
  let rec loop () =
    let n = try Unix.read s chunk 0 256 with Unix.Unix_error _ -> 0 in
    if n > 0 then (Buffer.add_subbytes b chunk 0 n; loop ())
  in
  loop ();
  Unix.close s;
  Buffer.contents b

let show_line l = String.concat "\\r" (String.split_on_char '\r' l)

let report path =
  let r = request path in
  Printf.printf "%s:\n" path;
  let rec find i = if i + 3 >= String.length r then None
    else if String.sub r i 4 = "\r\n\r\n" then Some i else find (i + 1) in
  match find 0 with
  | None -> Printf.printf "  no blank line; %d bytes: %S\n" (String.length r) r
  | Some i ->
      let head = String.sub r 0 (i + 2) and body = String.sub r (i + 4) (String.length r - i - 4) in
      List.iter (fun l -> if l <> "" then Printf.printf "  %s\n" (show_line l)) (String.split_on_char '\n' head);
      let cl = List.find_map (fun l ->
          match String.index_opt l ':' with
          | Some k when String.lowercase_ascii (String.sub l 0 k) = "content-length" ->
              Some (int_of_string (String.trim (String.sub l (k + 1) (String.length l - k - 1))))
          | _ -> None) (String.split_on_char '\n' head) in
      (match cl with
       | Some n when n = String.length body -> Printf.printf "  Content-Length = body bytes (%d)\n" n
       | Some n -> Printf.printf "  Content-Length %d, body bytes %d\n" n (String.length body)
       | None -> Printf.printf "  no Content-Length; body bytes %d\n" (String.length body));
      if String.length body <= 40 then Printf.printf "  body %S\n" body
      else Printf.printf "  body starts %S\n" (String.sub body 0 40)

let () =
  let oc = open_out_bin file in
  output_string oc "line one\nline two\n"; close_out oc;
  Unix.utimes file 1000000000.0 1000000000.0;
  ignore (Lm_thread.Thread.create (fun () -> Http_simple.serve_http start connect () 0) ());
  Mutex.lock m;
  while !port = 0 do Condition.wait c m done;
  Mutex.unlock m;
  print_endline (if !port > 0 then "server bound to a port" else "no port");
  Array.iteri (fun i _ -> report (Printf.sprintf "/code/%d" i)) codes;
  List.iter report [ "/page"; "/content"; "/error"; "/redirect"; "/channel"; "/cchannel" ];
  Sys.remove file;
  exit 0
