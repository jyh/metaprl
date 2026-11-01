(*
 * O95 D5 control (mojave, 2026-11-01): program 1's I4 (U == F) restated with
 * b0 in list{top} * int, the type programs 2-3 give it (program 1: top * int).
 * Scratch, not scored: it measures whether the type moves a program-1 count.
 *)
extends Vir

open Basic_tactics

interactive_rw router_fuse_l :
   ('b0 in list{top} * int) -->
   (all x: top. all k: int. wire_u32{'x; 'k} in int) -->
   (all x: int. all y: int. can_access{'x; 'y} in bool) -->
   (all x: int. has_tokens{'st; 'x} in bool) -->
   vir_U{'b0; 'st} <--> vir_F{'b0; 'st}
