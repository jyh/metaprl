(*
 * Time functions.
 *
 * ----------------------------------------------------------------
 *
 * Copyright (C) 2000 Jason Hickey, Caltech
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey
 * jyh@cs.caltech.edu
 *)

(*
 * Blown out representation.
 *)
type localtime =
   { time_sec : int;
     time_min : int;
     time_hour : int;
     time_mday : int;
     time_mon : int;
     time_year : int;
     time_zone : int
   }

(*
 * Convert a string to a float.
 *)
external localtime : int -> localtime = "c_localtime"
external mktime : localtime -> int = "c_mktime"

let parse_int s =
   try int_of_string s with
      Failure _ ->
         0

let month_of_name mon =
   match Latin1_case.lowercase mon with
      "jan" -> Some 0
    | "feb" -> Some 1
    | "mar" -> Some 2
    | "apr" -> Some 3
    | "may" -> Some 4
    | "jun" -> Some 5
    | "jul" -> Some 6
    | "aug" -> Some 7
    | "sep" -> Some 8
    | "oct" -> Some 9
    | "nov" -> Some 10
    | "dec" -> Some 11
    | _ -> None

(*
 * Days from 1970-01-01 to the civil date year-month-mday (month 1-12),
 * in the proleptic Gregorian calendar.
 *)
let days_from_civil year month mday =
   let year = if month <= 2 then year - 1 else year in
   let era = (if year >= 0 then year else year - 399) / 400 in
   let yoe = year - era * 400 in
   let mp = (month + 9) mod 12 in
   let doy = (153 * mp + 2) / 5 + mday - 1 in
   let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy in
      era * 146097 + doe - 719468

(*
 * The fields are a date and time in the named zone (GMT when unnamed);
 * the result is seconds since the epoch, UTC.  A two-digit year is
 * 2000-2049 below 50 and 1950-1999 otherwise.
 *)
let parse_date_aux mday mon year hour min sec zone =
   let mday = parse_int mday in
   let mon =
      match month_of_name mon with
         Some m -> m
       | None -> 0
   in
   let year =
      let year = parse_int year in
         if year < 50 then
            year + 2000
         else if year < 100 then
            year + 1900
         else
            year
   in
   let hour = parse_int hour in
   let min = parse_int min in
   let sec = parse_int sec in
   let zone =
      match Latin1_case.lowercase zone with
         "ut" | "gmt" | "utc" -> 0
       | "est" -> -5 * 60 * 60
       | "edt" -> -4 * 60 * 60
       | "cst" -> -6 * 60 * 60
       | "cdt" -> -5 * 60 * 60
       | "mst" -> -7 * 60 * 60
       | "mdt" -> -6 * 60 * 60
       | "pst" -> -8 * 60 * 60
       | "pdt" -> -7 * 60 * 60
       | _ -> 0
   in
      days_from_civil year (mon + 1) mday * 86400 + hour * 3600 + min * 60 + sec - zone

(*
 * The three forms of RFC 7231 7.1.1.1, and the form this read before:
 *    Sun, 06 Nov 1994 08:49:37 GMT       RFC 1123
 *    Sunday, 06-Nov-94 08:49:37 GMT      RFC 850
 *    Sun Nov  6 08:49:37 1994            asctime (GMT)
 *    [Sun] 06 Nov 1994 08 49 37 GMT
 * Anything else is 0.
 *)
let parse_time s =
   let fields = List.filter (fun f -> f <> "") (Lm_string_util.split " \t,:-" s) in
   let is_number f = try ignore (int_of_string f); true with Failure _ -> false in
      match fields with
         [wday; mon; mday; hour; minute; sec; year] when not (is_number wday) && month_of_name mon <> None ->
            parse_date_aux mday mon year hour minute sec "gmt"
       | [mday; month; year; hour; minute; sec; zone] ->
            parse_date_aux mday month year hour minute sec zone
       | [_; mday; month; year; hour; minute; sec; zone] ->
            parse_date_aux mday month year hour minute sec zone
       | _ ->
            0

(*
 * Month name.
 *)
let name_of_month = function
   1 -> "January"
 | 2 -> "February"
 | 3 -> "March"
 | 4 -> "April"
 | 5 -> "May"
 | 6 -> "June"
 | 7 -> "July"
 | 8 -> "August"
 | 9 -> "September"
 | 10 -> "October"
 | 11 -> "November"
 | 12 -> "December"
 | _ -> "Unknown"

(*
 * Convert to a string.
 *)
external ctime : int -> string = "c_ctime"
external simpletime : int -> string = "c_simpletime"

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
