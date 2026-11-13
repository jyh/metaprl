(* Http_simple's request-header parsers and multipart form bodies.

   Part 1, over loopback as in test_http_serve: one request carrying every
   header kind parse_header_entry names (but the dates, whose value is a
   time-zone-dependent float and which test_ctime covers), and the
   variants of Host, Cache-Control, If-Match and Referer; the handler
   prints the parsed entries in the order it receives them.  Part 2,
   direct: parse_post_body on multipart/form-data bodies, including the
   refusals.  No test reached parse_header_entry, the cache-control,
   host, if-match, URI or content-disposition parsers, or the multipart
   path (bisect at c013b0579 for the unit tests; a theory build or proof
   replay at 008a9607e does not run the web server).

   The expected file is the output of the code as written.  Pinned as
   found (only RequestCookies and RequestContentType have a reader outside
   this file, and RequestContentDisposition one inside the multipart path,
   so none of the header misreadings below reaches a user; the last item
   does):
   - the handler receives the entries last first;
   - Host: parse_host splits on white space, so "localhost:8080" is a host
     with no port, only "localhost 8080" yields a port, and an empty value
     is "unknown-host";
   - Cache-Control: the same splitter, so "max-age=60" is the extension
     "max-age=60" and only "max-age 60" is MaxAge; a two-word value is an
     Extension2, lowercased and unquoted;
   - Referer: parse_uri ends the host at the first "/", so
     "http://host:8080/p/q" has an empty host, no port and the path
     "/host:8080/p/q", "/local/path" (no colon) is all protocol, and only
     "http:host:8080/p" reads as host "host", port 8080 and path "p";
   - Pragma with any value is no-cache; a non-numeric Max-Forwards is 0;
   - Content-Disposition keeps the quotes of its parameter values (the
     multipart path unescapes the name);
   - multipart: a part with no Content-Disposition raises Not_found, the
     other refusals Failure; Shell_browser.get_post_body turns Not_found
     into an empty form, so such a post loses every field. *)
open Http_server_type

let port = ref 0
let m = Mutex.create ()
let c = Condition.create ()

let start t info =
  let i = Http_simple.http_info t in
  Mutex.lock m; port := i.http_port; Condition.signal c; Mutex.unlock m;
  info

let opt_int = function Some i -> string_of_int i | None -> "None"
let pairs l = "[" ^ String.concat "; " (List.map (fun (k, v) -> k ^ "=" ^ v) l) ^ "]"

let cache = function
  | CacheRequestNoCache -> "NoCache"
  | CacheRequestNoStore -> "NoStore"
  | CacheRequestMaxAge i -> "MaxAge " ^ string_of_int i
  | CacheRequestMaxStale i -> "MaxStale " ^ string_of_int i
  | CacheRequestMinFresh i -> "MinFresh " ^ string_of_int i
  | CacheRequestNoTransform -> "NoTransform"
  | CacheRequestOnlyIfCached -> "OnlyIfCached"
  | CacheRequestExtension0 s -> "Extension0 " ^ s
  | CacheRequestExtension1 s -> "Extension1 " ^ s
  | CacheRequestExtension2 (a, b) -> "Extension2 " ^ a ^ " " ^ b

let entry = function
  | RequestAccept s -> "Accept " ^ s
  | RequestAcceptCharset s -> "AcceptCharset " ^ s
  | RequestAcceptEncoding s -> "AcceptEncoding " ^ s
  | RequestAcceptLanguage s -> "AcceptLanguage " ^ s
  | RequestAuthorization s -> "Authorization " ^ s
  | RequestCacheControl d -> "CacheControl " ^ cache d
  | RequestConnection s -> "Connection " ^ s
  | RequestContentType ct ->
      Printf.sprintf "ContentType %s/%s %s" ct.content_type_main ct.content_type_sub (pairs ct.content_type_params)
  | RequestContentLength i -> "ContentLength " ^ string_of_int i
  | RequestContentDisposition d ->
      Printf.sprintf "ContentDisposition %s %s" d.content_disposition_type (pairs d.content_disposition_params)
  | RequestCookies l -> "Cookies " ^ pairs l
  | RequestDate _ -> "Date"
  | RequestExpect -> "Expect"
  | RequestFrom s -> "From " ^ s
  | RequestHost (h, p) -> Printf.sprintf "Host %s %s" h (opt_int p)
  | RequestIfMatch None -> "IfMatch *"
  | RequestIfMatch (Some l) -> "IfMatch [" ^ String.concat "; " l ^ "]"
  | RequestIfModifiedSince _ -> "IfModifiedSince"
  | RequestIfNoneMatch s -> "IfNoneMatch " ^ s
  | RequestIfRange s -> "IfRange " ^ s
  | RequestIfUnmodifiedSince _ -> "IfUnmodifiedSince"
  | RequestMaxForwards i -> "MaxForwards " ^ string_of_int i
  | RequestProxyAuthorization s -> "ProxyAuthorization " ^ s
  | RequestReferer u ->
      Printf.sprintf "Referer proto=%s host=%s port=%s path=%s" u.uri_proto u.uri_host (opt_int u.uri_port) u.uri_path
  | RequestTE s -> "TE " ^ s
  | RequestTrailer s -> "Trailer " ^ s
  | RequestTransferEncoding -> "TransferEncoding"
  | RequestUpgrade l -> "Upgrade [" ^ String.concat "; " l ^ "]"
  | RequestUserAgent s -> "UserAgent " ^ s
  | RequestVia s -> "Via " ^ s
  | RequestWarning s -> "Warning " ^ s
  | RequestExtension (t, s) -> "Extension " ^ t ^ ": " ^ s
  | _ -> "(another entry)"

let connect _t info out _inx _args header _body =
  List.iter (fun e -> Printf.printf "  %s\n%!" (entry e)) header;
  Http_simple.print_success_page out OkCode (Buffer.create 1);
  info

let request text =
  let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
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
  match String.split_on_char '\n' (Buffer.contents b) with
  | status :: _ when status <> "" -> String.trim status
  | _ -> "(no reply)"

let headers = [
  "Accept: text/html";
  "Accept-Charset: utf-8";
  "Accept-Encoding: gzip";
  "Accept-Language: en";
  "Authorization: Basic abc";
  "Cache-Control: no-cache";
  "Cache-Control: NO-STORE";
  "Cache-Control: max-age=60";
  "Cache-Control: max-age 60";
  "Cache-Control: max-stale 5";
  "Cache-Control: min-fresh 7";
  "Cache-Control: no-transform";
  "Cache-Control: only-if-cached";
  "Cache-Control: private";
  "Cache-Control: community \"UCI\"";
  "Cache-Control: a b c";
  "Connection: close";
  "Content-Type: Text/HTML; Charset=utf-8; q=1";
  "Content-Length: 0";
  "Content-Disposition: Form-Data; name=\"f\"; filename=\"a b.txt\"";
  "Cookie: a=1; b=x%20y; c";
  "Expect: 100-continue";
  "From: someone@example.org";
  "Host: localhost";
  "Host: localhost:8080";
  "Host: localhost 8080";
  "Host: ";
  "If-Match: *";
  "If-Match: \"e1\" \"e2\"";
  "If-None-Match: \"e3\"";
  "If-Range: \"e4\"";
  "Max-Forwards: 3";
  "Max-Forwards: many";
  "Pragma: whatever";
  "Proxy-Authorization: Basic def";
  "Referer: http://host:8080/p/q";
  "Referer: /local/path";
  "Referer: http:host:8080/p";
  "TE: trailers";
  "Trailer: Expires";
  "Transfer-Encoding: chunked";
  "Upgrade: h2c websocket";
  "User-Agent: test/1.0";
  "Via: 1.1 proxy";
  "Warning: 199 note";
  "X-Custom: value";
]

let ct_multipart boundary =
  { content_type_main = "multipart"; content_type_sub = "form-data"; content_type_params = [ "boundary", boundary ] }

let crlf l = String.concat "\r\n" l

let multipart = [
  "two fields", ct_multipart "XyZ",
  crlf [ "preamble"; "--XyZ"; "Content-Disposition: form-data; name=\"a\""; ""; "one"; "--XyZ";
         "Content-Disposition: form-data; name=\"b\"; filename=\"b.txt\""; "Content-Type: text/plain"; "";
         "two"; "lines"; "--XyZ--"; "epilogue" ];
  "empty value", ct_multipart "B",
  crlf [ "--B"; "Content-Disposition: form-data; name=\"e\""; ""; ""; "--B--" ];
  "name unquoted", ct_multipart "B",
  crlf [ "--B"; "Content-Disposition: form-data; name=u"; ""; "v"; "--B--" ];
  "no name", ct_multipart "B",
  crlf [ "--B"; "Content-Disposition: form-data; filename=\"x\""; ""; "v"; "--B--" ];
  "not form-data", ct_multipart "B",
  crlf [ "--B"; "Content-Disposition: attachment; name=\"x\""; ""; "v"; "--B--" ];
  "no disposition", ct_multipart "B",
  crlf [ "--B"; "Content-Type: text/plain"; ""; "v"; "--B--" ];
  "no boundary in the body", ct_multipart "B", "just text";
  "no boundary parameter", { (ct_multipart "B") with content_type_params = [] }, "--B--";
  "urlencoded", { content_type_main = "application"; content_type_sub = "x-www-form-urlencoded"; content_type_params = [] },
  "x=1&y=a+b%26&z";
  "other type", { content_type_main = "text"; content_type_sub = "plain"; content_type_params = [] }, "x=1";
]

let () =
  ignore (Lm_thread.Thread.create (fun () -> Http_simple.serve_http start connect () 0) ());
  Mutex.lock m;
  while !port = 0 do Condition.wait c m done;
  Mutex.unlock m;
  print_endline (if !port > 0 then "server bound to a port" else "no port");
  print_endline "headers, as the handler receives them:";
  let reply = request ("GET /h HTTP/1.0\r\n" ^ String.concat "" (List.map (fun h -> h ^ "\r\n") headers) ^ "\r\n") in
  Printf.printf "reply: %s\n" reply;
  print_endline "multipart:";
  List.iter (fun (name, ct, body) ->
      let r =
        try pairs (List.map (fun (k, v) -> k, String.escaped v) (Http_simple.parse_post_body ct body))
        with e -> "raises " ^ Printexc.to_string e
      in
      Printf.printf "  %-24s %s\n" name r) multipart;
  (* Leave without the at_exit teardown.  The server threads are still
     blocked in accept when the main thread exits; on Windows (mingw, OCaml
     4.14.4 and 5.4.1) the teardown let them accept again and log
     "Http_simple: End_of_file: error during web service" 1 to 12 times AFTER
     the last line of stdout, i.e. after exit had flushed it (master's Windows
     runs at cabd9e49, b70008d9, 6a0b2fa6; Linux and macOS never printed it).
     Every case above has been printed by then, so flushing and calling
     _exit, which ends the process with no cleanup, loses nothing the test
     checks. *)
  flush_all ();
  Unix._exit 0
