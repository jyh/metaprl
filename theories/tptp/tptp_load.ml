(*
 * Load a TPTP file and construct the sequent
 * that represents the goal.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
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
 * jyh@cs.cornell.edu
 *)

extends Tptp

open Lm_printf

open Term_sig
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan

open Itt_logic

open Tptp_type
open Tptp

(*
 * Compatibility.
 *)
let mk_var_term v =
   mk_var_term (Lm_symbol.add v)

let mk_all_term bvars t =
   mk_all_term (List.map Lm_symbol.add bvars) t

let mk_exists_term bvars t =
   mk_exists_term (List.map Lm_symbol.add bvars) t

(*
 * string -> path commands
 *)
let set_path _ var path =
   let path' = Lm_string_util.split ":" path in
      var := path'

let set_path_arg d var =
   Arg.String (set_path d var)

(*
 * This is a list of hosts to use for database lookup.
 *)
let path = Env_arg.general "tptp" ["."] "TPTP include directories" set_path set_path_arg

(*
 * Find a file in the path.
 *)
let open_in_path name =
   let rec open_file = function
      path :: paths ->
         begin
            let name = Filename.concat path name in
               try open_in name with
                  Sys_error msg ->
                     open_file paths
         end
    | [] ->
         eprintf "TPTP Error: can't open %s%t" name eflush;
         raise (Failure "open_in_path")
   in
      open_file !path

(*
 * The main entry point does the file handling.
 *)
let parse_tptp name =
   let rec collect name =
      let inx = open_in_path name in
      let rec collect_buf lexbuf =
         let clauses, command = Tptp_parse.program Tptp_lex.main lexbuf in
	       match command with
               FileComplete ->
                  close_in inx;
                  clauses
             | FileInclude name ->
                  clauses @ collect name @ collect_buf lexbuf
             | FileError ->
                  eprintf "TPTP Error: %s: syntax error at %d%t" name (Lexing.lexeme_start lexbuf) eflush;
                  clauses @ collect_buf lexbuf
      in
         collect_buf (Lexing.from_channel inx)
   in
      collect (name ^ ".p")

(*
 * Get a new variable name and put it in the substitution.
 *)
let new_var vars subst v =
   let v' = sprintf "X%d" vars in
      vars + 1, ((v, v') :: subst), v'

(*
 * The list saves the arity of the symbol in an association list.
 *)
let save_arity name symbols v arity =
   try
      let arity' = List.assoc v symbols in
         if arity' <> arity then
            raise (Failure (sprintf "Clause %s: symbol %s should have arity %d" name v arity));
         symbols
   with
      Not_found ->
         (* Add this symbol to the list *)
         (v, arity) :: symbols

(*
 * Compile an expression to a term.
 *    predp: true if the next symbol is a predicate symbol
 *    funs: assoc list of function symbol arities
 *    preds: assoc list of predicate symbol arities
 *    vars: list of variable names that have already been used
 *    subst: substitution of variable names
 *)
let rec compile_expr name predp funs preds vars subst = function
   NegExpr expr ->
      let funs, preds, vars, subst, expr = compile_expr name predp funs preds vars subst expr in
         funs, preds, vars, subst, mk_not_term expr
 | UidExpr v ->
      begin
         try
            let v = List.assoc v subst in
               funs, preds, vars, subst, mk_var_term v
         with
            Not_found ->
               let vars, subst, v = new_var vars subst v in
                  funs, preds, vars, subst, mk_var_term v
      end
 | FunExpr (v, subterms) ->
      if predp then
         let preds = save_arity name preds v (List.length subterms) in
         let funs, preds, vars, subst, exprs = compile_exprs name false funs preds vars subst subterms in
            funs, preds, vars, subst, mk_apply_term (mk_var_term v :: exprs)
      else
         let funs = save_arity name funs v (List.length subterms) in
         let funs, preds, vars, subst, exprs = compile_exprs name false funs preds vars subst subterms in
            funs, preds, vars, subst, mk_apply_term (mk_var_term v :: exprs)

and compile_exprs name predp funs preds vars subst = function
   expr :: exprs ->
      let funs, preds, vars, subst, expr = compile_expr name predp funs preds vars subst expr in
      let funs, preds, vars, subst, exprs = compile_exprs name predp funs preds vars subst exprs in
         funs, preds, vars, subst, expr :: exprs
 | [] ->
      funs, preds, vars, subst, []

(*
 * When the file is loaded,
 * we collect all predicate and function
 * symbols, and standardize-apart all
 * the clauses.
 *)
let compile_clause funs preds vars
    { clause_name = name;
      clause_type = ctype;
      clause_expr = exprs
    } =
   let funs, preds, vars, subst, exprs = compile_exprs name true funs preds vars [] exprs in
   let term =
      let bvars = List.map snd subst in
         if ctype = Axiom then
            mk_all_term bvars (mk_or_term exprs)
         else
            mk_exists_term bvars (mk_and_term exprs)
   in
      funs, preds, vars, term

let rec compile funs preds vars axioms goals = function
   clause :: clauses' ->
      begin
         let funs, preds, vars, clause' = compile_clause funs preds vars clause in
         let clause' = clause.clause_name, clause' in
            match clause.clause_type with
               Axiom ->
                  compile funs preds vars (clause' :: axioms) goals clauses'
             | Goal ->
                  compile funs preds vars axioms (clause' :: goals) clauses'
      end
 | [] ->
      funs, preds, List.rev axioms, List.rev goals

(*
 * Function are over Atom.
 *)
let atoms =
   [|<< atom0 >>;
     << atom1 >>;
     << atom2 >>;
     << atom3 >>;
     << atom4 >>;
     << atom5 >>
   |]

let mk_fun_decl (v, arity) =
   if arity > Array.length atoms then
      raise (Failure (sprintf "mk_fun_decl: arity is out of range: %d" arity))
   else
      Hypothesis (Lm_symbol.add v, atoms.(arity))

(*
 * Predicates are over atoms.
 *)
let props =
   [|<< prop0 >>;
     << prop1 >>;
     << prop2 >>;
     << prop3 >>;
     << prop4 >>;
     << prop5 >>
   |]

let mk_pred_decl (v, arity) =
   if arity > Array.length props then
      raise (Failure (sprintf "mk_pred_decl: arity is out of range: %d" arity))
   else
      Hypothesis (Lm_symbol.add v, props.(arity))

(*
 * Axiom declaration wrap a Hypothesis.
 *)
let mk_axiom_decl (v, ax) =
   Hypothesis (Lm_symbol.add v, ax)

(*
 * Collect the sequent.
 *)
let tptp_load name =
   let funs, preds, axioms, goals = compile [] [] 0 [] [] (parse_tptp name) in
   let hyps =
      (List.map mk_fun_decl funs) @
         (List.map mk_pred_decl preds) @
         (List.map mk_axiom_decl axioms)
   in
   let concl =
      match goals with
         [] ->
            eprintf "TPTP Warning: %s has no goals%t" name eflush;
            <<"false">>
       | [_, goal] ->
            goal
       | (_, goal) :: _ ->
            eprintf "TPTP Warning: %s has multiple goals%t" name eflush;
            goal
   in
   let seq =
      mk_sequent_term { sequent_args = <<sequent_arg>>;
                        sequent_hyps = SeqHyp.of_list hyps;
                        sequent_concl = concl
      }
   in
      seq

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
