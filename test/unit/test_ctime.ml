(* Ctime (mllib, with clib/c_time.c), which Http_simple uses to read the
   Date, If-Modified-Since and If-Unmodified-Since request headers.
   Checked against Unix.gmtime on 2,000 instants from 1970 to 2037, with TZ
   set inside the test so the result does not depend on the machine:
     - mktime (localtime t) = t, and localtime's fields against Unix
       (month 1-12, as c_localtime returns it), with TZ = UTC0;
     - parse_time of the date of t in each of the three forms an HTTP
       server must accept (RFC 7231 7.1.1.1: RFC 1123, RFC 850, asctime),
       and of the one form parse_time took, "06 Nov 1994 08 49 37 GMT".
   and the same with TZ = PST8PDT (daylight saving), where parse_time must
   give the same answers.  Until they were fixed:
     - parse_time returned 0 for all three HTTP forms (2000 of 2000 each):
       it split on whitespace only, so "08:49:37" was one field;
     - in the one form it took, every date was a month early: it numbered
       months from 0 and c_mktime subtracted 1 again;
     - c_mktime's memset(&time, sizeof(time), 0) had its arguments swapped,
       so tm_isdst was whatever the stack held: with TZ = PST8PDT, 966 of
       2,000 round trips were an hour off on macOS (undefined behaviour,
       so it was declared, not printed);
     - parse_time read the fields as local time (c_mktime), so the answer
       depended on the machine's zone.
   The generator is a fixed linear congruential sequence, not Random. *)
let state = ref 5
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state
let days = [| "Sun"; "Mon"; "Tue"; "Wed"; "Thu"; "Fri"; "Sat" |]
let longdays = [| "Sunday"; "Monday"; "Tuesday"; "Wednesday"; "Thursday"; "Friday"; "Saturday" |]
let mons = [| "Jan"; "Feb"; "Mar"; "Apr"; "May"; "Jun"; "Jul"; "Aug"; "Sep"; "Oct"; "Nov"; "Dec" |]
let forms = [
  "RFC 1123  Sun, 06 Nov 1994 08:49:37 GMT", (fun (g : Unix.tm) ->
      Printf.sprintf "%s, %02d %s %d %02d:%02d:%02d GMT" days.(g.tm_wday) g.tm_mday mons.(g.tm_mon) (g.tm_year + 1900) g.tm_hour g.tm_min g.tm_sec);
  "RFC 850   Sunday, 06-Nov-94 08:49:37 GMT", (fun g ->
      Printf.sprintf "%s, %02d-%s-%02d %02d:%02d:%02d GMT" longdays.(g.tm_wday) g.tm_mday mons.(g.tm_mon) (g.tm_year mod 100) g.tm_hour g.tm_min g.tm_sec);
  "asctime   Sun Nov  6 08:49:37 1994", (fun g ->
      Printf.sprintf "%s %s %2d %02d:%02d:%02d %d" days.(g.tm_wday) mons.(g.tm_mon) g.tm_mday g.tm_hour g.tm_min g.tm_sec (g.tm_year + 1900));
  "the old   06 Nov 1994 08 49 37 GMT", (fun g ->
      Printf.sprintf "%02d %s %d %02d %02d %02d GMT" g.tm_mday mons.(g.tm_mon) (g.tm_year + 1900) g.tm_hour g.tm_min g.tm_sec) ]

let classify d =
  if d = 0 then "exact"
  else if d < 0 && d >= -31 * 86400 && d <= -28 * 86400 then "a month early"
  else "other"

let () =
  let n = 2000 in
  List.iter (fun tz ->
  Unix.putenv "TZ" tz;
  let ts = List.init n (fun _ -> next () mod 2145916800) in  (* 1970 .. 2038 *)
  let rt = List.length (List.filter (fun t -> Ctime.mktime (Ctime.localtime t) = t) ts) in
  let lt = List.length (List.filter (fun t ->
      let l = Ctime.localtime t and g = Unix.gmtime (float_of_int t) in
      l.Ctime.time_sec = g.tm_sec && l.time_min = g.tm_min && l.time_hour = g.tm_hour
      && l.time_mday = g.tm_mday && l.time_mon = g.tm_mon + 1 && l.time_year = g.tm_year + 1900) ts) in
  Printf.printf "TZ = %s: mktime (localtime t) = t       %4d of %d\n" tz rt n;
  if tz = "UTC0" then Printf.printf "TZ = %s: localtime t = Unix.gmtime t    %4d of %d\n" tz lt n;
  List.iter (fun (name, fmt) ->
      let counts = Hashtbl.create 4 in
      let zero = ref 0 in
      List.iter (fun t ->
          let s = fmt (Unix.gmtime (float_of_int t)) in
          let p = Ctime.parse_time s in
          if p = 0 then incr zero
          else let k = classify (p - t) in Hashtbl.replace counts k (1 + try Hashtbl.find counts k with Not_found -> 0))
        ts;
      Printf.printf "TZ = %s: parse_time, %s: returns 0 %d" tz name !zero;
      List.iter (fun k -> match Hashtbl.find_opt counts k with
          | Some c -> Printf.printf ", %s %d" k c | None -> ())
        [ "exact"; "a month early"; "other" ];
      print_newline ())
    forms)
  [ "UTC0"; "PST8PDT" ];
  (* A named zone: 03:49:37 EST is 08:49:37 GMT, 784111777 (Unix). *)
  List.iter (fun s -> Printf.printf "parse_time %S = %d\n" s (Ctime.parse_time s))
    [ "Sun, 06 Nov 1994 08:49:37 GMT"; "Sun, 06 Nov 1994 03:49:37 EST"; "Sun, 06 Nov 1994 00:49:37 PST"; "not a date" ]
