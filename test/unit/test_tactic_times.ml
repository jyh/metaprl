(* Tactic_boot.times_used, the user and system time timingT prints: the
   time between two Unix.times readings, the process's own and its
   children's (tms_cutime, tms_cstime).  On fixed readings, so the result
   is the same on every OS, each line prints what times_used gives and the
   model: (finish utime + cutime) - (start utime + cutime), and the same
   for the system times.  The expected file is the output of the code as
   written (2026-11-14). *)
open Tactic_boot

let t u s cu cs = { Unix.tms_utime = u; tms_stime = s; tms_cutime = cu; tms_cstime = cs }
let model a b =
  (b.Unix.tms_utime +. b.Unix.tms_cutime) -. (a.Unix.tms_utime +. a.Unix.tms_cutime),
  (b.Unix.tms_stime +. b.Unix.tms_cstime) -. (a.Unix.tms_stime +. a.Unix.tms_cstime)

let show name a b =
  let u, s = TacticInternal.times_used a b in
  let mu, ms = model a b in
  Printf.printf "%-40s user %g system %g | model user %g system %g | %s\n" name u s mu ms
    (if (u, s) = (mu, ms) then "same" else "DIFFERENT")

let () =
  show "no children" (t 1. 2. 0. 0.) (t 4. 6. 0. 0.);
  show "children before, none during" (t 1. 2. 10. 20.) (t 4. 6. 10. 20.);
  show "children during, none before" (t 1. 2. 0. 0.) (t 4. 6. 100. 200.);
  show "children before and during" (t 1. 2. 10. 20.) (t 4. 6. 110. 220.);
  show "same reading" (t 1. 2. 10. 20.) (t 1. 2. 10. 20.)
