doc <:doc<
   @begin[doc]
   @module[M_closure]

   Closure conversion for the @emph{M} language.  The program is
   closed in four steps.

   @begin[enumerate]
   @item{In the first step, all @tt[LetRec] terms are replaced
      with @tt[CloseRec] terms, which include an extra frame
      parameter.  The frame is allocated as a tuple, and
      and the free variables are projected from the tuple.}

   @item{In the second step, for each @tt[CloseRec] that has a free
      variable, the free variable is added to the frame,
      and projected within the record.}

   @item{In the third step, the @tt[CloseRec] is converted back to
      a @tt[LetRec] followed by a tuple allocation.}

   @item{The fourth phase moves code around an generally cleans
      up.}
   @end[enumerate]

   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2003 Jason Hickey, Caltech

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
   @end[license]
>>

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>
extends Base_meta
extends M_ir
doc <:doc< @docoff >>

open M_ir
open M_util

open Basic_tactics

open Base_meta

(************************************************************************
 * REDUCTION RESOURCE                                                   *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @resources

   @bf{The @Comment!resource[closure_resource]}
   @docoff
   @end[doc]
>>
let resource (term * conv, conv) closure =
   table_resource_info extract_data

let closureTopC_env e =
   get_resource_arg (env_arg e) get_closure_resource

let closureTopC = funC closureTopC_env

let closureC =
   repeatC (higherC closureTopC)

(************************************************************************
 * Terms
 *)

doc <:doc<
   @begin[doc]
   @modsubsection{Terms}

   We define several auxiliary terms.

   The <<CloseVar{v. 'e['v]; 'a}>> term is the same as <<LetAtom{'a; v. 'e['v]}>>.
   We use a special term for variables that are being closed.

   The <<CloseRecVar{'R; 'frame}>> term is used to wrap record variables.
   The term represents the partial application of the record <<'R>> to
   the <<'frame>> variable.

   The <<CloseRec{R1, frame1. 'fields['R1; 'frame1];
                R2, frame2. 'body['R2; 'frame2];
                'length; 'tuple}>>
   is a recursive record definition.  The function defined by the
   <<'fields['R1; 'frame1]>> takes the <<'frame1>> as an extra argument; <<'frame1>>
   represents the environment containing all the functions' free variables.
   The <<'body['R2; 'frame2]>> is the rest of the program.  The <<'frame2>>
   represents the frame to be used for the functions in <<'R2>>.  The
   <<'frame2>> is allocated as the tuple, which has ``<<'length>>'' fields.

   <<CloseSubscript{'a1; 'a2; v. 'e['v]}>> is the same as @hrefterm[LetSubscript],
   but we use a special term to guide the closure conversion
   process.

   <<CloseFrame{frame. 'e['frame]}>> is the term that adds an extra
   frame argument to each of the functions in the record.
   @end[doc]
>>
declare CloseVar{v. 'e['v]; 'a}
declare CloseRecVar{'R; 'frame}
declare CloseRec{R1, frame1. 'fields['R1; 'frame1];
                 R2, frame2. 'body['R2; 'frame2];
                 'length;
                 'tuple}
declare CloseSubscript{'frame; 'index; v. 'e['v]}
declare CloseFrame{frame. 'e['frame]}

doc docoff

dform close_var_df : parens :: "prec"[prec_let] :: CloseVar{v. 'e; 'a} =
   bf["close "] slot{'v} bf[" = "] slot{'a} bf[" in"] hspace slot["lt"]{'e}

dform close_rec_var_df : CloseRecVar{'R; 'frame} =
   slot{'R} bf["["] slot{'frame} bf["]"]

dform close_rec_df : parens :: "prec"[prec_let] :: CloseRec{R1, frame1. 'e1; R2, frame2. 'e2; 'length; 'tuple} =
   szone szone pushm[3] bf["close rec "]
   slot{'R1} `"," slot{'frame1} `"." hspace 'e1 popm ezone
   hspace slot{'R2} `"," slot{'frame2} bf["."]
   hspace slot{'tuple} bf[" of length "] slot{'length}
   hspace slot["lt"]{'e2} ezone

dform close_subscript_df : parens :: "prec"[prec_let] :: CloseSubscript{'a1; 'a2; v. 'e} =
   szone bf["close "] slot{'v} bf[" = "] slot{'a1} bf[".["] slot{'a2} bf["] in"] hspace slot["lt"]{'e} ezone

dform close_frame : parens :: "prec"[prec_fun] :: CloseFrame{frame. 'e} =
   szone pushm[3] Nuprl_font!lambda Nuprl_font!subq slot{'frame} `"." hspace slot{'e} popm ezone

(*
 * ML functions on terms.
 *)
let close_var_term      = << CloseVar{v. 'e['v]; 'a} >>
let close_var_opname    = opname_of_term close_var_term
let is_close_var_term   = is_dep1_dep0_term close_var_opname
let dest_close_var_term = dest_dep1_dep0_term close_var_opname
let mk_close_var_term   = mk_dep1_dep0_term close_var_opname

let close_rec_term      = << CloseRec{R1, frame1. 'fields['R1; 'frame1]; R2, frame2. 'body['R2; 'frame2]; 'length; 'tuple} >>
let close_rec_opname    = opname_of_term close_rec_term
let is_close_rec_term   = is_dep2_dep2_dep0_dep0_term close_rec_opname
let dest_close_rec_term = dest_dep2_dep2_dep0_dep0_term close_rec_opname
let mk_close_rec_term   = mk_dep2_dep2_dep0_dep0_term close_rec_opname

doc <:doc<
   @begin[doc]
   @modsubsection{Phase 1}

   Convert all @tt[LetRec] to @tt[CloseRec] so that each function will
   have a frame variable for its free variables.
   @end[doc]
>>
prim_rw add_frame : LetRec{R1. 'fields['R1]; R2. 'e['R2]} <-->
   CloseRec{R1, frame. 'fields[CloseRecVar{'R1; 'frame}];
            R2, frame. 'e[CloseRecVar{'R2; 'frame}];
            Length[0:n];
            AllocTupleNil}

doc <:doc<
   @begin[doc]
   @modsubsection{Phase 2}

   In the first phase, we abstract free variables using inverse beta-reduction.
   That is, suppose we have a recursive definition:

   @begin[verbatim]
   close rec R, frame.
      fun f_1 = e_1
      ...
      fun f_n = e_n
   in ...
   @end[verbatim]

   and suppose that one of the function bodies $e_i$ has a free variable $v$.
   Then we first abstract the variable:

   @begin[verbatim]
   CloseVar{v. close rec ...; v}
   @end[verbatim]

   Next, we apply the close_frame rewrite, which takes the free
   variable, adds it to the frame, and projects it in the record.

   @begin[verbatim]
   close var v = a in
   close rec R, frame.
      fun f_1 = e_1
      ...
      fun f_n = e_n
   R, frame (length = i)(args) in
   ...

   close rec R, frame.
      let v = frame[i] in
      fun f_1 = e_1
      ...
      fun f_n = e_n
   R, frame (length = i + 1)(v :: args) in
   ...
   @end[verbatim]

   Variable closure is a beta-rewrite.
   @end[doc]
>>
prim_rw reduce_beta : CloseVar{v. 'e['v]; 'a} <--> 'e['a]

doc <:doc< @doc{This is the main function to lift out free variables.} >>
declare Length{'length}

prim_rw wrap_length : Length{meta_num[i:n]} <--> Length[i:n]

prim_rw close_frame :
   CloseVar{v. CloseRec{R1, frame1. 'fields['v; 'R1; 'frame1];
                        R2, frame2. 'body['v; 'R2; 'frame2];
                        Length[i:n];
                        'tuple};
            'a} <-->
   CloseRec{R1, frame1. CloseSubscript{AtomVar{'frame1}; AtomInt[i:n]; v. 'fields['v; 'R1; 'frame1]};
            R2, frame2. LetAtom{AtomVar{'a}; v. 'body['v; 'R2; 'frame2]};
            Length{meta_sum[i:n, 1:n]};
            AllocTupleCons{AtomVar{'a}; 'tuple}}

doc docoff

dform length_df : Length{'t} = math_it["Length"] `"(" 't `")"

doc <:doc<
   @begin[doc]
   Now, a conversional to apply the inverse-beta reduction.
   The <<'vars>> parameter is the set of function variables.
   Function variables are not treated as free; we don't
   need closure conversion for them.
   @end[doc]
>>
let abstractTopC =
   let convC e =
      let t = env_term e in
         if is_close_rec_term t then
            let r1, frame1, fields, r2, frame2, body, length, tuple = dest_close_rec_term t in
            let vars = [r1; frame1; r2; frame2] in
            let rec search fv =
               match fv with
                  v :: fv ->
                     if List.mem v vars then
                        search fv
                     else
                        let t = mk_close_var_term v t (mk_var_term v) in
                           foldC t reduce_beta
                           thenC close_frame
                           thenC addrC[2; 0] reduce_meta_sum
                           thenC addrC[2] wrap_length
                | [] ->
                     failC
            in
               search (free_vars_list fields)
         else
            failC
   in
      funC convC

doc <:doc<
   @begin[doc]
   @modsubsection{Phase 3}

   Convert the @tt[CloseRec] term to a @tt[LetRec] plus a frame allocation.
   @end[doc]
>>
prim_rw close_close_rec :
   CloseRec{R1, frame1. 'fields['R1; 'frame1];
            R2, frame2. 'body['R2; 'frame2];
            'length;
            'tuple} <-->
   LetRec{R1. CloseFrame{frame1. 'fields['R1; 'frame1]};
          R2. LetTuple{'length; 'tuple; frame2. 'body['R2; 'frame2]}}

doc <:doc<
   @begin[doc]
   @modsubsection{Phase 4}

   Generally clean up and move code around.
   @end[doc]
>>
prim_rw close_fields :
   CloseSubscript{'a1; 'a2; v. Fields{'fields['v]}} <-->
   Fields{CloseSubscript{'a1; 'a2; v. 'fields['v]}}

prim_rw close_fundef :
   CloseSubscript{'a1; 'a2; v1. FunDef{'label; AtomFun{v2. 'e['v1; 'v2]}; 'rest['v1]}} <-->
   FunDef{'label; AtomFun{v2. LetSubscript{'a1; 'a2; v1. 'e['v1; 'v2]}}; CloseSubscript{'a1; 'a2; v1. 'rest['v1]}}

prim_rw close_enddef :
   CloseSubscript{'a1; 'a2; v. EndDef} <--> EndDef

prim_rw close_frame_fields :
   CloseFrame{frame. Fields{'fields['frame]}} <-->
   Fields{CloseFrame{frame. 'fields['frame]}}

prim_rw close_frame_fundef :
   CloseFrame{frame. FunDef{'label; AtomFun{v. 'e['frame; 'v]}; 'rest['frame]}} <-->
   FunDef{'label; AtomFun{frame. AtomFun{v. 'e['frame; 'v]}}; CloseFrame{frame. 'rest['frame]}}

prim_rw close_frame_enddef :
   CloseFrame{frame. EndDef} <--> EndDef

prim_rw close_let_subscript :
   LetSubscript{'a1; 'a2; v1. AtomFun{v2. 'e['v1; 'v2]}} <-->
   AtomFun{v2. LetSubscript{'a1; 'a2; v1. 'e['v1; 'v2]}}

prim_rw close_initialize_1 :
   LetClosure{'a1; 'a2; v. Initialize{'e['v]}} <-->
   Initialize{LetClosure{'a1; 'a2; v. 'e['v]}}

prim_rw close_initialize_2 :
   LetTuple{'length; 'tuple; v. Initialize{'e['v]}} <-->
   Initialize{LetTuple{'length; 'tuple; v. 'e['v]}}

(*
 * Actually build the closure.
 *)
prim_rw close_let_fun :
   LetFun{CloseRecVar{'R; 'frame}; 'label; v. 'e['v]} <-->
   LetClosure{AtomFunVar{'R; 'label}; AtomVar{'frame}; v. 'e['v]}

(*
 * Optimize closures just before tailcalls.
 *)
prim_rw close_tailcall :
   LetClosure{'f; 'frame; g. TailCall{AtomVar{'g}; 'args}} <-->
   TailCall{'f; ArgCons{'frame; 'args}}

(*
 * Add all these rules to the closure resource.
 *)
let resource closure +=
    [<< CloseSubscript{'a1; 'a2; v. Fields{'fields['v]}} >>, close_fields;
     << CloseSubscript{'a1; 'a2; v1. FunDef{'label; AtomFun{v2. 'e['v1; 'v2]}; 'rest['v1]}} >>, close_fundef;
     << CloseSubscript{'a1; 'a2; v. EndDef} >>, close_enddef;
     << CloseFrame{frame. Fields{'fields['frame]}} >>, close_frame_fields;
     << CloseFrame{frame. FunDef{'label; AtomFun{v. 'e['frame; 'v]}; 'rest['frame]}} >>, close_frame_fundef;
     << CloseFrame{frame. EndDef} >>, close_frame_enddef;
     << LetFun{CloseRecVar{'R; 'frame}; 'label; v. 'e['v]} >>, close_let_fun;
     << LetSubscript{'a1; 'a2; v1. AtomFun{v2. 'e['v1; 'v2]}} >>, close_let_subscript;
     << LetClosure{'a1; 'a2; v. Initialize{'e['v]}} >>, close_initialize_1;
     << LetTuple{'length; 'tuple; v. Initialize{'e['v]}} >>, close_initialize_2;
     << LetClosure{'f; 'frame; g. TailCall{AtomVar{'g}; 'args}} >>, close_tailcall]

doc docoff

(* These are the main tactics. *)

let frameT =
   repeatT (rwh add_frame 0)

let abstractT =
   repeatT (rwh abstractTopC 0)

let uncloseT =
   repeatT (rwh close_close_rec 0)

let pushT =
   rw closureC 0

let closeT =
   frameT
   thenT abstractT
   thenT uncloseT
   thenT pushT

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
