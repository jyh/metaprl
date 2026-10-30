(* Ctime (mllib, with clib/c_time.c), which Http_simple uses to read the
   Date, If-Modified-Since and If-Unmodified-Since request headers.
   Checked against Unix.gmtime on 2,000 instants from 1970 to 2037, with TZ
   set inside the test so the result does not depend on the machine:
     - mktime (localtime t) = t, and localtime's fields against Unix
       (month 1-12, as c_localtime returns it), with TZ = UTC0;
     - parse_time of the date of t in each of the three forms an HTTP
       server must accept (RFC 7231 7.1.1.1: RFC 1123, RFC 850, asctime),
       and of the one form parse_time took, "06 Nov 1994 08 49 37 GMT".
   Recorded as found:
     - parse_time returns 0 for all three HTTP forms: it splits on
       whitespace only, so "08:49:37" is one field and the date has six,
       and it takes only seven or eight;
     - in the form it takes, the month is one too early: parse_time numbers
       months from 0 and c_mktime subtracts 1 again;
     - (declared, not printed: it is undefined behaviour) c_mktime calls
       memset(&time, sizeof(time), 0), arguments swapped, so tm_isdst is
       whatever the stack held; under a zone with daylight saving that
       read 966 of 2,000 instants an hour off on macOS.
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
  Unix.putenv "TZ" "UTC0";
  let n = 2000 in
  let ts = List.init n (fun _ -> next () mod 2145916800) in  (* 1970 .. 2038 *)
  let rt = List.length (List.filter (fun t -> Ctime.mktime (Ctime.localtime t) = t) ts) in
  let lt = List.length (List.filter (fun t ->
      let l = Ctime.localtime t and g = Unix.gmtime (float_of_int t) in
      l.Ctime.time_sec = g.tm_sec && l.time_min = g.tm_min && l.time_hour = g.tm_hour
      && l.time_mday = g.tm_mday && l.time_mon = g.tm_mon + 1 && l.time_year = g.tm_year + 1900) ts) in
  Printf.printf "TZ = UTC0: mktime (localtime t) = t       %4d of %d\n" rt n;
  Printf.printf "TZ = UTC0: localtime t = Unix.gmtime t    %4d of %d\n" lt n;
  List.iter (fun (name, fmt) ->
      let counts = Hashtbl.create 4 in
      let zero = ref 0 in
      List.iter (fun t ->
          let s = fmt (Unix.gmtime (float_of_int t)) in
          let p = Ctime.parse_time s in
          if p = 0 then incr zero
          else let k = classify (p - t) in Hashtbl.replace counts k (1 + try Hashtbl.find counts k with Not_found -> 0))
        ts;
      Printf.printf "parse_time, %s: returns 0 %d" name !zero;
      List.iter (fun k -> match Hashtbl.find_opt counts k with
          | Some c -> Printf.printf ", %s %d" k c | None -> ())
        [ "exact"; "a month early"; "other" ];
      print_newline ())
    forms
