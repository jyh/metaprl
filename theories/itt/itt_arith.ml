(*
 * This is an unfinished version of arith.
 * Right now jus the sequent parsing is implemented.
 *
 * We implement the arith procedure in the Nuprl book on page 173.
 * We use our own data structures for the sequent, and the formulas
 * here.
 *)

include Itt_int
include Itt_equal
include Itt_logic

open Printf
open Debug

open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError

open Itt_int
open Itt_equal
open Itt_logic

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_arith%t" eflush

let debug_arith =
   create_debug (**)
      { debug_name = "arith";
        debug_description = "display arith operations";
        debug_value = false
      }

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * A monomial is always represented in normal form as
 *    c * atom list
 * which is the product of the constant with the atoms
 * in the list.  The atoms are sorted in ascending order.
 *)
type mono = Num.num * int list

(*
 * Monomials are eventually converted to linear forms.
 *)
type linear = Num.num * int

(*
 * A polynomial is always represented in a normal form as
 *    mono list,
 * where the monomials in the list are sorted in lexicographic
 * order based on their atom lists.  There are no monomials
 * with dusplicate atom lists, because they cand be combined.
 *)
type 'a poly = 'a list

(*
 * An expression is a formula before it is
 * normalized to a polynomial.
 *)
type expr =
   Number of Num.num
 | Atom of int
 | Sum of expr * expr
 | Diff of expr * expr
 | Prod of expr * expr

(*
 * Possible formulas.
 *)
type 'a form =
   LessThan of 'a * 'a
 | Equal of 'a * 'a
 | Or of 'a form * 'a form
 | And of 'a form * 'a form
 | Implies of 'a form * 'a form
 | Not of 'a form

(*
 * Arith forms just include inequalities and equality.
 *)
type 'a opt =
   OptLessThan of 'a * 'a
 | OptEqual of 'a * 'a

(*
 * A sequent has some hypotheses and conclusions.
 *)
type 'a seq =
   { hyps : 'a list;
     goals : 'a list
   }

(*
 * Unknown formulas are represented as atoms,
 * and we save them in an array for later
 * well-formedness accounting.  Each atom
 * respresents an unknown term, or a polynomial
 * of such terms, without a constant value.
 *)
type atom_value =
   AtomTerm of term
 | AtomPoly of mono poly

(*
 * The table has an index for creating new atoms,
 * and it has a table for lookuing up previous terms.
 *)
type 'a table =
   { mutable index : int;
     table : ('a, int) Hashtbl.t
   }

(************************************************************************
 * NORMALIZATION                                                        *
 ************************************************************************)

(*
 * Compare two atom lists.
 *)
let rec compare_atoms_atoms = function
   h1 :: t1, h2 :: t2 ->
      if h1 = h2 then
         compare_atoms_atoms (t1, t2)
      else
         h1 - h2
 | [], [] ->
      0
 | [], _ :: _ ->
      -1
 | _ :: _, [] ->
      1

(*
 * Polynomials are always represented so atom lists
 * are in lexcographic order.
 *)
let normalize_poly poly =
   let compare (_, atoms1) (_, atoms2) =
      compare_atoms_atoms (atoms1, atoms2) < 0
   in
   let poly = Sort.list compare poly in
   let rec collect ((c1, atoms1) as mono1) = function
      ((c2, atoms2) as mono2) :: t ->
         if atoms1 = atoms2 then
            collect (Num.add_num c1 c2, atoms1) t
         else
            mono1 :: collect mono2 t
    | [] ->
         [mono1]
   in
      match poly with
         mono :: poly ->
            collect mono poly
       | [] ->
            []

(*
 * Linear combination of two polynomials.
 *)
let rec linear_poly_poly f = function
   ((h1 :: t1) as poly1), ((h2 :: t2) as poly2) ->
      let i1, atoms1 = h1 in
      let i2, atoms2 = h2 in
      let rel = compare_atoms_atoms (atoms1, atoms2) in
         if rel < 0 then
            h1 :: linear_poly_poly f (t1, poly2)
         else if rel = 0 then
            (f i1 i2, atoms1) :: linear_poly_poly f (t1, t2)
         else
            h2 :: linear_poly_poly f (poly1, t2)
 | [], poly2 ->
      poly2
 | poly1, [] ->
      poly1

let add_poly_poly poly1 poly2 =
   linear_poly_poly Num.add_num (poly1, poly2)

let sub_poly_poly poly1 poly2 =
   linear_poly_poly Num.sub_num (poly1, poly2)

(*
 * Multiply polynomials.
 *)
let mul_mono_poly mono poly =
   let rec mul i1 atoms1 = function
      (i2, atoms2) :: t ->
         (Num.mult_num i1 i2, Sort.merge (<) atoms1 atoms2) :: (mul i1 atoms1 t)
    | [] ->
         []
   in
   let i1, atoms1 = mono in
      mul i1 atoms1 poly

let mul_poly_poly poly1 poly2 =
   let rec mul poly1 poly2 =
      match poly1 with
         h :: t ->
            add_poly_poly (mul_mono_poly h poly2) (mul t poly2)
       | [] ->
            []
   in
      normalize_poly (mul poly1 poly2)

(*
 * Create a polynomial from an expression.
 *)
let rec poly_of_expr = function
   Sum (expr1, expr2) ->
      add_poly_poly (poly_of_expr expr1) (poly_of_expr expr2)
 | Diff (expr1, expr2) ->
      sub_poly_poly (poly_of_expr expr1) (poly_of_expr expr2)
 | Prod (expr1, expr2) ->
      mul_poly_poly (poly_of_expr expr1) (poly_of_expr expr2)
 | Atom i ->
      [Num.Int 1, [i]]
 | Number i ->
      [i, []]

(*
 * Map a function over the expressions in the formula.
 *)
let rec form_map f = function
   LessThan (expr1, expr2) ->
      LessThan (f expr1, f expr2)
 | Equal (expr1, expr2) ->
      Equal (f expr1, f expr2)
 | Or (form1, form2) ->
      Or (form_map f form1, form_map f form2)
 | And (form1, form2) ->
      And (form_map f form1, form_map f form2)
 | Implies (form1, form2) ->
      Implies (form_map f form1, form_map f form2)
 | Not form ->
      Not (form_map f form)

(*
 * Find a polynomial in the hashtable.
 *)
let find_poly table poly =
   let { table = hash; index = index } = table in
      try Hashtbl.find hash poly with
         Not_found ->
            let index = index + 1 in
               Hashtbl.add hash poly index;
               table.index <- index;
               index

(*
 * Now convert the polynomial formula to a formula with
 * the polynomials linearized.
 *)
let rec linear_form_of_expr_form table form =
   let linear_of_expr table expr =
      match poly_of_expr expr with
         (i, []) :: t ->
            i, find_poly table t
       | t ->
            Num.Int 0, find_poly table t
   in
      form_map (linear_of_expr table) form

(************************************************************************
 * PARSING                                                              *
 ************************************************************************)

(*
 * Find an expression in the table.
 * If the term is not found, create a new atom.
 *)
let find_expr table t =
   let { table = hash; index = index } = table in
      try Atom (Hashtbl.find hash t) with
         Not_found ->
            let index = index + 1 in
               Hashtbl.add hash t index;
               table.index <- index;
               Atom index

(*
 * Parse an expression.
 * This is just multiplication, addition, subtraction.
 *)
let rec parse_expr table t =
   if is_natural_number_term t then
      Number (dest_natural_number t)
   else if is_mul_term t then
      let left, right = dest_mul t in
         Prod (parse_expr table left, parse_expr table right)
   else if is_add_term t then
      let left, right = dest_add t in
         Sum (parse_expr table left, parse_expr table right)
   else if is_sub_term t then
      let left, right = dest_sub t in
         Diff (parse_expr table left, parse_expr table right)
   else
      find_expr table t

(*
 * Parse a single statement.
 * We keep a hash table of terms that have
 * been mapped to new variables.
 *)
let rec parse_form table t =
   if is_lt_term t then
      let left, right = dest_lt t in
         LessThan (parse_expr table left, parse_expr table right)

   else if is_le_term t then
      (* LE means not greater than *)
      let left, right = dest_le t in
         Not (LessThan (parse_expr table right, parse_expr table left))

   else if is_equal_term t then
      let t, a, b = dest_equal t in
         if t = int_term then
            Equal (parse_expr table a, parse_expr table b)
         else
            raise (RefineError ("parse_form", StringError "equality is not over int"))

   else if is_ge_term t then
      (* GE means not less than *)
      let left, right = dest_ge t in
         Not (LessThan (parse_expr table left, parse_expr table right))

   else if is_gt_term t then
      let left, right = dest_gt t in
         LessThan (parse_expr table right, parse_expr table left)

   else if is_or_term t then
      let left, right = dest_or t in
         Or (parse_form table left, parse_form table right)

   else if is_and_term t then
      let left, right = dest_and t in
         And (parse_form table left, parse_form table right)

   else if is_not_term t then
      Not (parse_form table (dest_not t))

   else
      raise (RefineError ("parse_form", StringError ("formula is not valid")))

(*
 * As hyps are parsed, non-arithmetic forms are skipped.
 *)
let rec parse_hyps table = function
   hd :: tl ->
      begin
         match hd with
            Hypothesis (_, t)  ->
               begin
                  try parse_form table t :: parse_hyps table tl with
                     RefineError _ ->
                        (* Some hyps are not formulas *)
                        parse_hyps table tl
               end
          | Context _ ->
               parse_hyps table tl
      end
 | [] ->
      []

(*
 * As conclusions are parsed, non-arithemetic forms are skipped.
 *)
let rec parse_goals table = function
   hd :: tl ->
      begin
         try parse_form table hd :: parse_goals table tl with
            RefineError _ ->
               parse_goals table tl
      end
 | [] ->
      []

(*
 * Collect the atom bindings by enumerating the table.
 *)
let collect_atoms f table result =
   let result = ref [] in
   let collect t i =
      result := f t i :: !result
   in
      Hashtbl.iter collect table

(*
 * Sort the atoms into an array.
 * There are no holes and no duplicates.
 *)
let sort_atoms atoms =
   let atoms = Sort.list (fun (i, _) (j, _) -> i < j) atoms in
      if !debug_arith then
         begin
            let rec check i = function
               (i', _) :: t ->
                  if i = i' then
                     check (i + 1) t
                  else
                     raise (Failure "Itt_arith.sort_atoms: bogus atom collection")
             | [] ->
                  ()
            in
               eprintf "Itt_arith.sort_atoms: checking for missing and duplicate atoms%t" eflush;
               check 1 atoms;
               eprintf "Itt_arith.sort_atoms: atom list checked%t" eflush
         end;
      Array.of_list (List.map snd atoms)

(*
 * Parse the sequent.
 * We return the sequent and an array of atom values.
 *)
let sequent_of_term t =
   let { sequent_hyps = hyps; sequent_goals = goals } = explode_sequent t in
   let table = { index = 0; table = Hashtbl.create 97 } in
   let hyps = parse_hyps table hyps in
   let goals = parse_goals table goals in
   let table' = { index = table.index; table = Hashtbl.create 97 } in
   let seq =
      { hyps = List.map (linear_form_of_expr_form table') hyps;
        goals = List.map (linear_form_of_expr_form table') goals
      }
   in
   let atoms = ref [] in
      collect_atoms (fun t i -> i, AtomTerm t) table.table atoms;
      collect_atoms (fun p i -> i, AtomPoly p) table'.table atoms;
      seq, sort_atoms !atoms

(************************************************************************
 * TABLEAU                                                              *
 ************************************************************************)

(*
 * This is the function that needs to be implemented.
 * jyh: I'm postponing this for now.
 *)
let search seq =
   raise (RefineError ("arith", StringError "not implemented"))

(************************************************************************
 * PROOF GENERATION                                                     *
 ************************************************************************)

(*
 * We reduce the proof to its axioms.
 * Also postponed.
 *)
let justify proof table =
   raise (RefineError ("arith", StringError "not implemented"))

(************************************************************************
 * ARITH                                                                *
 ************************************************************************)

(*
 * H >- T
 * by arith
 *
 * This is the large decision procedure.
 *)
mlterm arith_check{'t} =
   let seq, table = sequent_of_term <:con< 't >> in
   let proof = search seq in
      justify proof table
 | fun _ _ ->
      raise (RefineError ("arith", StringError "not implemented"))

prim arith : arith_check{'t} --> 't = it

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
