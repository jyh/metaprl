(*
 * This module defines a "forward-chaining" cache that performs
 * forward -chaining, as well as collecting statistics about
 * hyp usage.  The module is expressed in terms of inherited
 * and synthesized attributes.
 *
 * Notes:
 *
 * "Worlds" are a technique that we use for incremental chaining.
 * Inferences are relative to a collection of assumptions ("hypotheses")
 * that together form a "world."  When assumptions are added
 * in the course of refinement, new worlds are created, and when
 * the user backs out of a proof, either because it failed, or
 * because it is complete, hypotheses are removed to form
 * more general worlds.
 *
 * The issues that have to be solved for incremental computation:
 * When new hypotheses are added, more things can be derived
 * by forward chaining.  Howver, any further inferences that are
 * derived in the old worlds should remain valid in those worlds,
 * wso that if we back out, the inferences are preserved.
 *
 * Unfortunately, refinement and backout are not very compatible.
 * Data structures:
 *     rules: a collection of rules together with inferences
 *         that may be used as arguments.
 *     infs: inferences derived by forward chaining.
 *     goals: goals derived by backward chaining.
 *
 * Constraint: backout is common, and it chould be cheap.
 *    Also it should be easy to recover if an inference is
 *    backed out and later restored.  Call this "recovery".
 * Tradeoff: if backout is cheap, then lookup and insertion
 *    becomes expensive.
 *
 * If we only had refinement, then we could just keep one version
 * of "rules".  However, with backout, we need to recover old rule
 * sets.  "rules" is implemented as a hash table.
 *
 * There are two implementations I can think of.
 *
 * First, the rule table can be implemented as a set of tables,
 * one for each world.  Backout is easy: just remove tables from
 * the set.  Insertion is somewhat expensive, because a rule table has
 * to be selected for insertion.  Lookup is expensive, because
 * a lookup has to be performed in all tables.  If outdated
 * tables are retained, recovery should restore an old table
 * to the set, but forward chaining must be restarted to
 * allow the restored inferences to be combined with other
 * inferences added during their abscence.
 *
 * Second, make one rule table and tag the inferences in the
 * table with a "version" (which is really just the world in which they
 * were originally inferred).  If there is no garbage collection,
 * backout is easy, by outdated some revisions.  Insertion is
 * constant time.  Lookup is more difficult, because outdated inferences
 * must be filtered out.  Garbage collection must examine every item
 * in the table.  If forward chaining is performed through outdated
 * inferences, recovery is trivial, but the chaining can get carried
 * away with irrelevant inferences.  If forward chaining does not include
 * outdated inferences, then it must be restarted on inference
 * that are restored.
 *
 * As a whole, the second option seems more reasonable.  And that is
 * the option impelemented in this module.  Haven't decided whether to chain
 * through outdated inferences.  The "goal" table is global, except at a
 * world change.  Example:
 *        H >> A * (B -> C)         (global)
 *        (H >> A) & (H >> B -> C)  (and intro, global)
 *                   (H; B >> C)    (imp intro, local)
 *
 * There is a global backchain list, and a queue of pending
 * goals.  Goals that have been backed out are put on a
 * postponement list.
 *
 * There is a global inference list, and a global forward chaining
 * queue.  Inferences can be moved off of this queue onto a
 * postponement queue if their world is backed out.
 *
 * $Log$
 * Revision 1.4  1998/04/21 20:58:10  jyh
 * Fixed typing problems introduced by refiner msequents.
 *
 * Revision 1.3  1998/04/08 15:08:37  jyh
 * Moved precedence to mllib.
 *
 * Revision 1.2  1998/04/08 14:57:37  jyh
 * ImpDag is in mllib.
 *
 * Revision 1.1  1997/04/28 15:52:42  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 * Revision 1.4  1996/11/13 22:58:43  jyh
 * Initial version of forward/backward chaining cache.
 *
 * Revision 1.3  1996/11/05 02:42:40  jyh
 * This is a version of the FCache with complete forward chaining,
 * and multiple worlds.  Untested.
 *
 * Revision 1.2  1996/11/01 01:25:16  jyh
 * This is version of the cache for pure forward chaining.
 * Right now, I am thinking about extending the chainer with "worlds,"
 * which will be necessary to incorporate backward chaining.
 *
 *)

open Term
open Term_template
open Rewrite

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * A forward-chaining rule.
 * The justification (which is probably going to be a tactic),
 * takes the indices of the hyps as arguments, takes
 * the names of the results, and produces an 'a (which is
 * probably a tactic).
 *)
type 'a frule =
   { fc_ants : term list;
     fc_concl : term list;
     fc_just : 'a
   }

(*
 * Similar back-chaining rule.
 *)
type 'a brule =
   { bc_concl : term;
     bc_ants : (term list * term) list;
     bc_just : 'a
   }

(*
 * A proof has a forward and a backward component.
 *)
type 'a proof =
   ForeTactics of (int list * 'a) list
 | BackTactic of ('a * 'a proof list)
 | NthHyp of int
 | SeqTactic of 'a proof list

(*
 * The fcache is a collection of compiled rules.
 * The plates are templates for the arguments.
 * If there is a wild entry, it contains a
 * list of indices of arguments that are wildcards
 * (variables), and the rewrite converts the args
 * to their wildcard entries.
 *)
type 'a fcacheInfo =
   { finfo_plates : term_template list;
     finfo_wild : (int list * rewrite_rule) option;
     finfo_rw : rewrite_rule;
     finfo_just : 'a
   }

(*
 * A backward info entry has a template for the goal,
 * and a rewrite to produce the subgoals.
 *)
type 'a bcacheInfo =
   { binfo_plate : term_template;
     binfo_rw : term -> (term list * term) list;
     binfo_just : 'a
   }

(*
 * The cache is a list of these entries.
 *)
type 'a cache =
   { cache_finfo : 'a fcacheInfo list;
     cache_binfo : 'a bcacheInfo list
   }

(*
 * An inference is a fact, either because it is a
 * hypothesis, or because it has been derived by
 * forward chaining.  The info contains the justification,
 * the inferences that were used as antecedents, and
 * the total list of results.  A particular inference
 * is a specific result.
 *)
type 'a inferenceInfo =
   { inf_values : term list;
     inf_just : 'a;
     inf_args : 'a inference list;
     inf_world : 'a world
   }
   
and 'a hypInfo =
   { hyp_world : 'a world }
   
and 'a infInfo =
   Inference of 'a inferenceInfo
 | Hyp of 'a hypInfo

and 'a inference =
   { inf_name : string;
     inf_value : term;
     inf_hash : term_template;
     inf_info : 'a infInfo
   }

(*
 * A goal is just a term.  It may depend on a conjunction of
 * goals, or it may be justified by a forward chained inference.
 * In some cases, the goal will become dependent on a particular world.
 * In that case, list the extra assumptions, as well as the world
 * that has been constructed.
 *
 * The subgoals are either unexplored, or they are a list of
 * possible subgoal combinations (meaning that they represent
 * an or-and branch).
 *)
and 'a subgoal =
   { sub_goals : 'a goal list;
     sub_just : 'a
   }

and 'a subgoals =
   Unexplored
 | Unsolvable
 | Subgoals of 'a subgoal list
   
and assumption =
   { assum_term : term;
     assum_hash : term_template
   }

and 'a goal =
   { goal_goal : term;
     goal_hash : term_template;
     goal_assums : assumption list;
     mutable goal_subgoals : 'a subgoals
   }
   
(*
 * The search DAG is a bi-directional DAG of goals, with
 * a flag indicating if the goal is satisfied.  The goal
 * can either be satisfied by forward chaining, or it
 * can be derived from subgoals.
 *
 * Unproved: hasn't been explored
 * Unprovable: can't explore this goal
 * Derivable: can be derived from proof of subgoals
 * Primitive: provable by forward chaining
 * Derived: proof by backward chaining
 *)
and 'a node_status =
   Unproved
 | Unprovable
 | Derivable
 | Derived
 | Primitive of 'a inference
   
and 'a goalnode =
   { node_goal : 'a goal;
     node_world : 'a world;
     mutable node_children : 'a goalnode list list;
     mutable node_status : 'a node_status
   }
   
(*
 * Stack is always OR-AND branching.
 *)
and 'a goalitem =
   AndBranch
 | OrBranch
 | Node of 'a goalnode
 | RootNode of 'a goalnode

(*
 * A "world" is a collection of assumptions (hypotheses).
 * Each world contains a new assumption that is added to an
 * older world.
 *
 * All the inferences made by forward chaining are listed here.
 * If the assumption is derivable from a previous world, the
 * infs may be associated with that previous world.
 *)
and 'a world_info =
   { world_hyp : 'a inference;
     world_prev : 'a world;
     mutable world_infs : 'a inference list
   }

and 'a world =
   Hypothesis of 'a world_info
 | Empty

(*
 * Forward chaining table.
 * The flookupTable maps terms into possible arguments to rules.
 *)
type 'a flookupTable = (term_template, (int * 'a fcacheInfo) list) Hashtbl.t

(*
 * Backward chaining table.
 * A backward table maps goals into rules.
 *)
type 'a blookupTable = (term_template, 'a bcacheInfo list) Hashtbl.t

(*
 * This info table list possible instantiations of rules.
 * Each rule contains a list of possible instantiations,
 * where the instantation is expressed as a vector of
 * possible arguments, where the arguments are a list
 * of inferences that are derived from the relevant hyps.
 * The argument lists are updated destructively.
 *)
type 'a infoTable =
   (term_template list, ('a fcacheInfo * 'a inference list array) list) Hashtbl.t

(*
 * Table of terms.  Each term can be satisfied by an inference,
 * and it may also be listed as a goal.
 *)
type 'a termEntry =
   { entry_infs : 'a inference list;
     entry_goals : 'a goal list
   }

type 'a termTable = (term_template, 'a termEntry) Hashtbl.t

(*
 * Backward chaining tree table.
 * This maps goals to nodes in the DAG.
 * This will coded to have the type:
 *    'a goal -> 'a goalnode
 *)
type 'a bchainTable = (term_template, 'a goalnode list) Hashtbl.t

(*
 * The extract contains:
 * Static lookup tables:
 *    ext_ftable: A hashtable of the rules for forward chaining.
 *       The hashtable maps terms to antecedents of rules,
 *       so that when a new fact arrives, it is easy to
 *       tell how the new fact can be used.
 *    ext_btable: A hashtable of the rules for backward chaining
 *
 * Tables to optimize inferencing:
 *    ext_terms: a table mapping terms to all inferences
 *        and goals having the same term.
 *    ext_rules: a table containg possible instations of
 *        the forward chaining rules.
 *
 * Hyp info.  The lists all have the length ext_hcount.
 *    ext_hcount: number of hyps
 *    ext_names: the internal names of the hyps
 *    ext_gnames: the external names of the hyps
 *    ext_hyps: the hyp lost
 *
 * For hyp records:
 *    ext_used: a list of hyps that have been referenced.
 *
 * For forward chaining:
 *    ext_index: number of inferences ever made
 *    ext_fqueue: a list of inferences available for forward chaining
 *
 * For backward chaining:
 *    ext_goal: the goal in the current world
 *    ext_node: the node corresponding to this goal
 *    ext_bchain: the function that incrementally performs back chaining.
 *    ext_goals: the table mapping goals to nodes in the goal tree.
 *
 * All the worlds ever seen are also recorded.
 *    ext_world: the current world
 *    ext_worlds: all worlds investigated so far.
 *
 * All info particular to the current world is stored
 * in the extract directly.  All info that is common
 * to all worlds is stored in ext_base.
 *)
type 'a chain =
   {  (* Rule tables *)
      ext_ftable : 'a flookupTable;
      ext_btable : 'a blookupTable;
      ext_terms : 'a termTable;
      ext_rules : 'a infoTable;

      (* Forward chaining *)
      mutable ext_index : int;
      mutable ext_fqueue : 'a inference list;
      
      (* Possible worlds *)
      mutable ext_worlds : 'a world list
   }

type 'a extract =
   {  (* Assumptions *)
      ext_used : 'a world list;
      ext_hcount : int;
      ext_names : string list;
      ext_gnames : string list;
      ext_hyps : 'a world list;
      
      (* Backward chaining *)
      ext_goal : 'a goal option;
      ext_node : 'a goalnode option;
      ext_goals : 'a bchainTable;
      ext_bchain : 'a extract -> bool;

      (* Current world *)
      ext_world : 'a world;
      
      (* Chaining base *)
      ext_base : 'a chain
   }

(*
 * A synthesis just contains the handles of the used hyps.
 *)
type 'a synthesis =
   { syn_extract : 'a extract;
     syn_used : 'a world list
   }

(************************************************************************
 * BASIC UTILITIES                                                      *
 ************************************************************************)

(*
 * Construct a new name from the base.
 *)
let mk_var_name { ext_base = { ext_index = index } as base } =
   base.ext_index <- index + 1;
   "`" ^ (string_of_int index)

(*
 * Functional record update.
 *)
let set_used 
    { ext_used = used;
      ext_hcount = hcount;
      ext_names = names;
      ext_gnames = gnames;
      ext_hyps = hyps;
      ext_goal = goal;
      ext_node = node;
      ext_goals = goals;
      ext_bchain = bchain;
      ext_world = world;
      ext_base = base
    } used' =
   { ext_used = used';
     ext_hcount = hcount;
     ext_names = names;
     ext_gnames = gnames;
     ext_hyps = hyps;
     ext_goal = goal;
     ext_node = node;
     ext_goals = goals;
     ext_bchain = bchain;
     ext_world = world;
     ext_base = base
   }

let set_gnames
    { ext_used = used;
      ext_hcount = hcount;
      ext_names = names;
      ext_gnames = gnames;
      ext_hyps = hyps;
      ext_goal = goal;
      ext_node = node;
      ext_goals = goals;
      ext_bchain = bchain;
      ext_world = world;
      ext_base = base
    } gnames' =
   { ext_used = used;
     ext_hcount = hcount;
     ext_names = names;
     ext_gnames = gnames';
     ext_hyps = hyps;
     ext_goal = goal;
     ext_node = node;
     ext_goals = goals;
     ext_bchain = bchain;
     ext_world = world;
     ext_base = base
   }

(*
 * Get the world for any kind of inference.
 *)
let world_of_inf { inf_info = info } =
   match info with
      Inference { inf_world = world } -> world
    | Hyp { hyp_world = world } -> world

(*
 * World naming.
 *)
let name_of_world = function
   Hypothesis { world_hyp = { inf_name = name } } -> name
 | Empty -> raise (Invalid_argument "name_of_world")

(*
 * Push an inference into a world.
 *)
let push_world_inf world inf =
   match world with
      Hypothesis w ->
         w.world_infs <- inf::w.world_infs
    | Empty ->
         raise (Invalid_argument "push_world_inf")

(*
 * Forward chaining queue.
 *)
let push_extract_inf { ext_base = base } inf =
   base.ext_fqueue <- inf :: base.ext_fqueue

(************************************************************************
 * HASHTABLE IMPLEMENTATIONS                                            *
 ************************************************************************)

(*
 * Equality of goals.
 * Don't compare subgoals.
 *)
let eq_goal
    { goal_goal = t;
      goal_hash = hash;
      goal_assums = assums
    }
    { goal_goal = t';
      goal_hash = hash';
      goal_assums = assums'
    } =
   let rec aux = function
      ({ assum_term = t; assum_hash = hash }::tl),
      ({ assum_term = t'; assum_hash = hash' }::tl') ->
         if hash = hash' & alpha_equal t t' then
            aux (tl, tl')
         else
            false
    | [], [] ->
         true
    | _ ->
         false
   in
      hash = hash' & alpha_equal t t' & aux (assums, assums')

(*
 * Determine if a world is a prefix of another.
 * Useful for looking up inferences.
 *)
let is_child child parent =
   let rec aux world =
      if world == parent then
         true
      else
         match world with
            Hypothesis { world_prev = prev } ->
               aux prev
          | Empty ->
               false
   in
      aux child

(*
 * Determine if a world is an extension by the given assumptions.
 *)
let is_world_extension child assums parent =
   let rec aux world = function
      { assum_term = t; assum_hash = hash }::tl ->
         begin
            match world with
               Hypothesis { world_hyp = { inf_value = t';
                                          inf_hash = hash'
                                        };
                            world_prev = prev
               } ->
                  if hash = hash' & alpha_equal t t' then
                     aux prev tl
                  else
                     false
             | Empty ->
                  false
         end
    | [] ->
         world == parent
   in
      aux child assums

(*
 * Provide a 'a goal -> 'a goalnode interface to a 'a bchainTable.
 * Not idempotent.
 *)
let bset_tbl_node tbl ({ node_goal = { goal_hash = hash } } as node) =
   let nodes =
      try Hashtbl.find tbl hash with
         Not_found -> []
   in
      Hashtbl.remove tbl hash;
      Hashtbl.add tbl hash (node :: nodes)

let bset_node { ext_goals = tbl } = bset_tbl_node tbl

let bget_nodes
    ({ ext_goals = tbl })
    ({ goal_hash = hash } as goal) =
   let rec aux = function
      ({ node_goal = goal' } as node)::tl ->
         if goal' == goal then
            node::(aux tl)
         else
            aux tl
    | [] ->
         []
   in
   let l =
      try Hashtbl.find tbl hash with
         Not_found -> []
   in
      aux l

(*
 * This gets just one node with the given world,
 * extended by the assumptions in the goal.
 *)
let bget_node extract world ({ goal_assums = assums } as goal) =
   let nodes = bget_nodes extract goal in
   let test { node_world = world' } =
      is_world_extension world' assums world
   in
      List_util.find test nodes

(*
 * Provide a rough
 * term -> (int * 'a fcacheInfo) list interface for flookupTable.
 * Not idempotent.
 *)
let fset_entry tbl hash entry =
   let entries =
      try Hashtbl.find tbl hash with
         Not_found -> []
   in
      Hashtbl.remove tbl hash;
      Hashtbl.add tbl hash (entry::entries)

let fget_entry { ext_base = { ext_ftable = tbl; ext_rules = rules } } { inf_hash = hash } =
   let aux (i, ({ finfo_plates = plates } as rule)) =
      let test (rule', _) = rule' == rule in
      let rules = Hashtbl.find rules plates in
      let _, insts = List_util.find test rules in
         i, rule, insts
   in
   let l = Hashtbl.find tbl hash in
      List.map aux l

let init_insts tbl ({ finfo_plates = plates } as rule) =
   let len = List.length plates in
   let entry = Array.create len [] in
   let entries =
      try Hashtbl.find tbl plates with
         Not_found -> []
   in
      Hashtbl.remove tbl plates;
      Hashtbl.add tbl plates ((rule, entry) :: entries)

let fset_insts { ext_base = { ext_rules = rules } }
    ({ finfo_plates = plates } as rule)
    insts =
   let rec aux = function
      ((rule', _) as h)::tl ->
         if rule' == rule then
            (rule', insts)::tl
         else
            h::(aux tl)
    | [] -> []
   in
   let l = Hashtbl.find rules plates in
      aux l

(*
 * Provide a rough
 * 'a goal -> 'a bcacheInfo list interface for blookupTable.
 * Not idempotent.
 *)
let bset_entry tbl ({ binfo_plate = hash } as entry) =
   let entries =
      try Hashtbl.find tbl hash with
         Not_found -> []
   in
      Hashtbl.remove tbl hash;
      Hashtbl.add tbl hash (entry::entries)

let bget_entries { ext_base = { ext_btable = tbl } } { goal_hash = hash } =
   Hashtbl.find tbl hash

(*
 * Provide an interface to the terms table.
 * Not idempotent.
 *)
let set_inf
    { ext_base = { ext_terms = terms } }
    ({ inf_hash = hash } as inf) =
   let { entry_infs = infs; entry_goals = goals } =
      try Hashtbl.find terms hash with
         Not_found -> { entry_infs = []; entry_goals = [] }
   in
      Hashtbl.remove terms hash;
      Hashtbl.add terms hash { entry_infs = inf::infs; entry_goals = goals }

let set_goal
    { ext_base = { ext_terms = terms } }
    ({ goal_hash = hash } as goal) =
   let { entry_infs = infs; entry_goals = goals } =
      try Hashtbl.find terms hash with
         Not_found -> { entry_infs = []; entry_goals = [] }
   in
      Hashtbl.remove terms hash;
      Hashtbl.add terms hash { entry_infs = infs; entry_goals = goal::goals }

(*
 * Inferences are found by their term, and their world.
 *)
let find_inf
    { ext_base = { ext_terms = terms } }
    world t hash =
   let test ({ inf_value = t' } as inf) =
      let world' = world_of_inf inf in
         alpha_equal t t' & is_child world world'
   in
   let { entry_infs = infs } = Hashtbl.find terms hash in
      List_util.find test infs

let already_known extract world t hash =
   try
      find_inf extract world t hash; true
   with
      Not_found -> false

let find_goal
    { ext_base = { ext_terms = terms } }
    ({ goal_hash = hash } as goal) =
   let { entry_goals = goals } = Hashtbl.find terms hash in
      List_util.find (eq_goal goal) goals

(*
 * Find the goalnodes that match the inference.
 *)
let find_nodes
    ({ ext_base = { ext_terms = terms };
       ext_goals = btable
     } as extract)
    { inf_value = t; inf_hash = hash; inf_info = info } =
   let world =
      match info with
         Inference { inf_world = world' } -> world'
       | Hyp { hyp_world = world' } -> world'
   in
   let rec filter_goals = function
      ({ goal_goal = t' } as goal)::tl ->
         if alpha_equal t t' then
            goal::(filter_goals tl)
         else
            filter_goals tl
    | [] -> []
   in
   let rec filter_nodes = function
      ({ node_world = world' } as node)::tl ->
         if is_child world world' then
            node::(filter_nodes tl)
         else
            filter_nodes tl
    | [] -> []
   in
   let { entry_goals = goals } = Hashtbl.find terms hash in
   let goals' = filter_goals goals in
   let nodes = List_util.flat_map (bget_nodes extract) goals' in
      filter_nodes nodes

(*
 * Find an inference that proves the current goal.
 * The Hashtbl.find operation will *always* work because the
 * goal itself is in the table.
 *)
let find_inf_for_node
    { ext_base = { ext_terms = terms } }
    { node_goal = { goal_goal = t; goal_hash = hash };
      node_world = world
    } =
   let rec aux = function
      ({ inf_value = t' } as inf)::tl ->
         let world' = world_of_inf inf in
            if alpha_equal t t' & is_child world world' then
               Some inf
            else
               aux tl
    | [] ->
         None
   in
   let { entry_infs = infs } = Hashtbl.find terms hash in
      aux infs

let is_provable extract goal =
   match find_inf_for_node extract goal with
      Some _ -> true
    | None -> false

(*
 * See if a goal is already known.
 *)
let hash_goal { ext_base = { ext_terms = terms } }
    ({ goal_goal = t; goal_hash = hash } as goal) =
   let { entry_goals = goals } = Hashtbl.find terms hash in
      List_util.find (eq_goal goal) goals
      
(************************************************************************
 * UTILITIES                                                            *
 ************************************************************************)

(*
 * Find the wild terms, and mix them in with
 * the normal terms.  The nargs is a list of
 * indices of the wildcard entries.
 *)
let mix_wild nargs terms wilds =
   let rec aux terms wild i = function
      j::t ->
         begin
            if i = j then
               match wilds with
                  whd::wtl ->
                     whd::(aux terms wtl (i + 1) t)
                | [] ->
                     raise (Invalid_argument "mix_wild")
            else
               match terms with
                  thd::ttl ->
                     thd::(aux ttl wilds (i + 1) t)
                | [] ->
                     raise (Invalid_argument "mix_wild")
         end
    | [] ->
         terms
   in
      aux terms wilds 0 nargs

(*
 * Find a world that is a single extension
 * of the current one.  If there isn't an existing one,
 * raise Not_found.
 *)
let find_world_extension
    { ext_base = { ext_worlds = worlds } }
    world t hash =
   let rec aux = function
      (Hypothesis { world_hyp = { inf_value = t'; inf_hash = hash' };
                    world_prev = prev
       } as world')::tl ->
         if hash = hash' & prev == world & alpha_equal t t' then
            Some world'
         else
            aux tl
    | _::tl ->
         aux tl
    | [] ->
         None
   in
      aux worlds

(*
 * Find a hyp in the current world if it exists,
 * or create a new one.  Return the new world, but
 * do not link it into the complete list of worlds.
 * Assume that find_world_extension failed.
 *)
let build_world_with_hyp ({ ext_base = base } as extract) world t hash =
   try
      let inf = find_inf extract world t hash in
      let world' = world_of_inf inf in
         if is_child world world' then
            [], Hypothesis ({ world_hyp = inf;
                              world_prev = world;
                              world_infs = []
                            })
         else
            raise Not_found
   with
      Not_found ->
         let name = mk_var_name extract in
         let rec inf =
            { inf_name = name;
              inf_value = t;
              inf_hash = hash;
              inf_info = Hyp { hyp_world = world' }
            }
         and world' =
            Hypothesis { world_hyp = inf;
                         world_prev = world;
                         world_infs = [inf]
            }
         in
            set_inf extract inf;
            [inf], world'

(*
 * Find or build a world that is an extension of the current one.
 * Add newly generated inferences to the forward chaining queue.
 *)
let build_world_extension ({ ext_base = base } as extract) world assums =
   let rec aux world = function
      { assum_term = t; assum_hash = hash }::tl ->
         let world' =
            match find_world_extension extract world t hash with
               Some world' -> world'
             | None ->
                  let infs, world' = build_world_with_hyp extract world t hash in
                     base.ext_worlds <- world'::base.ext_worlds;
                     base.ext_fqueue <- infs @ base.ext_fqueue;
                     world'
         in
            aux world' tl
            
    | [] ->
         world
   in
      aux world assums

(************************************************************************
 * BACKWARD CHAINING                                                    *
 ************************************************************************)

(*
 * Build a subgoal list from a collection of antecendents.
 *)
let construct_subgoals extract just ants =
   let make_assum t =
      { assum_term = t;
        assum_hash = compute_template t
      }
   in
   let aux (args, t) =
      let goal =
         { goal_goal = t;
           goal_hash = compute_template t;
           goal_assums = List.map make_assum args;
           goal_subgoals = Unexplored
         }
      in
         try hash_goal extract goal with
            Not_found -> goal
   in
      { sub_goals = List.map aux ants;
        sub_just = just
      }

(*
 * Set the subgoals of a goal given a list of bcacheInfo
 * that may match this goal.
 *)
let set_subgoals extract ({ goal_goal = t } as goal) binfo =
   let rec aux = function
      { binfo_rw = rw; binfo_just = just }::tl ->
         begin
            try
               let ants = rw t in
               let _, subgoals' = aux tl in
                  true, (construct_subgoals extract just ants) :: subgoals'
            with
               _ -> aux tl
         end
    | [] ->
         false, []
   in
   let flag, subgoals = aux binfo in
      if flag then
         goal.goal_subgoals <- Subgoals subgoals
      else
         goal.goal_subgoals <- Unsolvable;
      flag

(*
 * Expand a goal to find its subgoals.
 * It is assumed that the goal is not directly provable
 * from an inference.
 *)
let expand_subgoals extract ({ goal_subgoals = subgoals } as goal) =
   match subgoals with
      Subgoals _ ->
         true
    | Unsolvable ->
         false
    | Unexplored ->
         set_subgoals extract goal (bget_entries extract goal)

(*
 * Construct a node from a subgoal.
 *)
let construct_node extract world ({ goal_assums = assums } as goal) =
   try bget_node extract world goal with
      Not_found ->
         (* Construct a new node *)
         let world' = build_world_extension extract world assums in
         let node =
            { node_goal = goal;
              node_world = world';
              node_children = [];
              node_status = Unproved
            }
         in
            bset_node extract node;
            node

(*
 * Set the children of the node from a subgoal list.
 *)
let find_node_children extract { node_world = world } subgoals =
   let construct' = construct_node extract world in
   let aux { sub_goals = goals } =
      List.map construct' goals
   in
      List.map aux subgoals

(*
 * Once the goal has been expanded, expand the node in the tree.
 * In the process, we hash the outgoing subgoals to squash
 * the DAG.
 *)
let set_node_children
    extract
    ({ node_goal =
         { goal_subgoals = subgoals } as goal
    } as node) =
   match subgoals with
      Unsolvable ->
         node.node_status <- Unprovable
    | Subgoals subgoals' ->
         node.node_status <- Derivable;
         node.node_children <- find_node_children extract node subgoals'
    | Unexplored ->
         raise (Invalid_argument "set_node_children")
   
(*
 * Expand a backward chain on a specific node in the tree.
 * Assume that node_status is Unproved.
 *)
let expand_node extract ({ node_goal = goal } as node) =
   match find_inf_for_node extract node with
      Some inf ->
         node.node_status <- Primitive inf
    | None ->
         begin
            if expand_subgoals extract goal then
               set_node_children extract node
            else
               node.node_status <- Unprovable
         end

(*
 * Stack operations for searching.
 * Here is and example stack:
 *     ...
 *     Node node1a
 *     Node node2a
 *     AndBranch
 *     Node node1b
 *     Node node2b
 *     Node node3b
 *     AndBranch
 *     Node node1c
 *     OrBranch
 *     Node node1d
 *     ....
 *     Node node1e
 *     RootNode rootnode
 *
 * The nodes directly above and AndBranch must all be true.
 * One of the AndBranches above an OrBranch must be true.
 * The OrBranch belongs to the node directly below it.
 * The Node above the RootNode must be true.
 *
 * Algorithm:
 *     1. If the top is a node:
 *        If it is unprovable, pop to AndBranch, and start the next branch.
 *        If it is proved, pop it.
 *        Otherwise, expand it and place the subgoals on the stack.
 *     2. If the top is an AndBranch:
 *        All the subgoals succeeded, so pop to this node (which is
 *        right below the OrBranch), and note that it is proved.
 *     3. If the top is an OrBranch:
 *        All the subgoals failed, so fail the node right below.
 *     4. If the top is a RootNode, then see if it succeeded.
 *        If so, we are done.
 *        If not, try again, and hope something was proved by
 *        forward chaining.
 *)

(*
 * Push the subgoals of an expanded node.
 *)
let push_derivable_node subgoals fstack =
   let rec aux = function
      subgoals::tl ->
         (List.map (function node -> Node node) subgoals) @ (AndBranch :: aux tl)
    | [] ->
         OrBranch :: !fstack
   in
      fstack := aux subgoals

(* Pop last and-branch *)
let pop_failed_branch fstack =
   let rec aux = function
      AndBranch::t -> t
    | _::t -> aux t
    | [] -> failwith "pop_failed_branch: empty stack"
   in
      fstack := aux !fstack

(*
 * This node succeeded because one of its
 * and-branches succeeded.
 *)
let pop_succeeded_node fstack =
   let rec aux = function
      OrBranch::(Node node)::t ->
         begin
            match node.node_status with
               Derivable ->
                  node.node_status <- Derived;
                  t
             | Derived | Primitive _ ->
                  t
             | Unproved | Unprovable ->
                  failwith "pop_succeeded_node: unprovable"
         end
    | _::t ->
         aux t
    | [] ->
         failwith "pop_succeeded_node: empty stack"
   in
      fstack := aux !fstack

(*
 * This creates a new function to perform backward chaining from a single
 * goal.  The backward chainer checks if the goal is provable.  If so, it
 * modifies the tree node to reflect a primitive proof.  If not, it
 * expands the goal into subgoals.
 *
 * Assume the new ext_goals table is empty.
 *
 * The search function keeps a stack of search functions,
 * and calls them until the stack is empty.
 *)
let new_bchain node =
   (* Search engine *)
   let fstack = ref [RootNode node] in
   let search_node extract ({ node_status = status; node_children = subgoals } as node) =
      match status with
         Unproved ->
            (* Expand subgoals, and restart *)
            expand_node extract node
            
       | Unprovable ->
            (* Failed node *)
            pop_failed_branch fstack
            
       | Derivable ->
            (* Push the subgoals *)
            push_derivable_node subgoals fstack
            
       | Derived | Primitive _ ->
            (* This node is provable *)
            Ref_util.pop fstack;
            ()
                  
   in
   let search extract =
      (* Process the top goal *)
      match List.hd !fstack with
         Node node ->
            (* Expand this node *)
            search_node extract node;
            false

       | AndBranch ->
            (* Success of all items in this branch *)
            pop_succeeded_node fstack;
            false
                  
       | OrBranch ->
            (* All subgoals failed, pop the node, and fail its branch *)
            Ref_util.pop fstack;
            pop_failed_branch fstack;
            false

       | RootNode node ->
            (* Is this node successful *)
            begin
               match node.node_status with
                  Unproved | Derivable ->
                     (* Try backward chaining *)
                     Ref_util.push (Node node) fstack;
                     false
                | Unprovable ->
                     (* Maybe this will be proved later by forward chaining *)
                     false
                | Derived | Primitive _ ->
                     true
            end
   in
      search

(*
 * Construct a new table and bchain.
 *)
let new_goals world goal =
   let tbl = Hashtbl.create 97 in
      match goal with
         Some goal' ->
            let node =
               { node_goal = goal';
                 node_world = world;
                 node_children = [];
                 node_status = Unproved
               }
            in
               bset_tbl_node tbl node;
               Some node, tbl, new_bchain node
      
       | None ->
            None, tbl, (function _ -> false)

(************************************************************************
 * FORWARD CHAINING                                                     *
 ************************************************************************)

(*
 * Update any of the outstanding goals in the goal tree.
 *)
let update_goalnodes extract inf =
   let status = Primitive inf in
   let aux node =
      node.node_status <- status
   in
   let nodes = find_nodes extract inf in
      List.iter aux nodes

(*
 * Build the results from the values produced
 * during rewriting.
 *)
let build_results ({ ext_base = base } as extract) world root values =
   let rec aux = function
      t::tl ->
         let hash = compute_template t in
            if already_known extract world t hash then
               aux tl
            else
               let inf =
                  { inf_name = mk_var_name extract;
                    inf_value = t;
                    inf_hash = hash;
                    inf_info = root
                  }
               in
                  push_world_inf world inf;
                  push_extract_inf extract inf;
                  update_goalnodes extract inf;
                  aux tl
    | [] ->
         ()
   in
      aux values

(*
 * Try all combinations of the args.
 *)
let instantiate f world insts =
   let rec aux world l = function
      h::t ->
         let aux' h' =
            let world' = world_of_inf h' in
               if is_child world world' then
                  aux world (h'::l) t
               else if is_child world' world then
                  aux world' (h'::l) t
               else
                  ()
         in
            List.iter aux' h
    | [] ->
         f world l
   in
      aux world [] insts

(*
 * Try to chain through a particular arglist.
 *)
let try_arglist_normal
    ({ ext_base = base } as extract)
    rw just world args =
   let terms = List.map (function inf -> inf.inf_value) args in
      try
         let values, _ = apply_rewrite rw ([||], [||]) terms in
         let root =
            Inference { inf_values = values;
                        inf_just = just;
                        inf_args = args;
                        inf_world = world
            }
         in
            build_results extract world root values
      with
         _ -> ()

(*
 * Try to chain through the new item.
 *)
let try_fchain_normal extract world { finfo_rw = rw; finfo_just = just } finst =
   let try_arglist_normal' = try_arglist_normal extract rw just in
      if not (List.mem [] finst) then
         instantiate try_arglist_normal' world (List.rev finst)

(*
 * Try a particular arglist in the wildcard mode.
 * nargs: the indices of the wild args
 * wrw: the rewrite to produce the wildcard hyps
 * rw: the rewrite to produce the results
 * just: the justification
 * args: the facts to be used
 *
 * produce a new extract info
 *)
let try_arglist_wild extract rw wrw nargs just world args =
   let terms = List.map (function inf -> inf.inf_value) args in
      try let wilds, _ = apply_rewrite wrw ([||], [||]) terms in
          let wargs = List.map (function t -> find_inf extract world t (compute_template t)) wilds in
          let values, _ = apply_rewrite rw ([||], [||]) terms in
          let facts = mix_wild nargs args wargs in
          let root =
             Inference { inf_values = values;
                    inf_just = just;
                    inf_args = facts;
                    inf_world = world
             }
          in
             build_results extract world root values
      with
         _ -> ()

(*
 * In wildcard chaining, some of the args are wildcards.
 * A rewrite is supplied to produce what these wildcard arguments
 * should be.
 *)
let try_fchain_wild extract world { finfo_rw = rw; finfo_just = just } (wargs, wrw) finst =
   let try_arglist_wild' = try_arglist_wild extract rw wrw wargs just in
      if not (List.mem [] finst) then
         instantiate try_arglist_wild' world (List.rev finst)

(*
 * Try chaining through a particular new item.
 * Optimize the case where there are no wildcard entries.
 *)
let try_fchain extract world ({ finfo_wild = wild } as info) finst =
   match wild with
      None -> try_fchain_normal extract world info finst
    | Some wild -> try_fchain_wild extract world info wild finst

(*
 * Try chaining through a particular new fact.
 *)
let try_fchaining extract inf (i, rule, insts) =
   let len = Array.length insts in
   let rec aux j =
      if j = len then
         []
      else if j = i then
         [inf] :: (aux (j + 1))
      else
         (insts.(j)) :: (aux (j + 1))
   in
   let finst = aux 0 in
   let world = world_of_inf inf in
      insts.(i) <- inf :: (insts.(i));
      try_fchain extract world rule finst

(*
 * Get something from the queue, and try to chain through it.
 *)
let fchain ({ ext_base = { ext_fqueue = fqueue } as base } as extract) =
   match fqueue with
      inf::tl ->
         base.ext_fqueue <- tl;
         let rules =
            try fget_entry extract inf with
               Not_found -> []
         in
            List.iter (try_fchaining extract inf) rules

    | [] ->
         ()

(************************************************************************
 * CHAIN COMMAND                                                        *
 ************************************************************************)

(*
 * Alternate forward and backward chaining.
 * Return true if a proof is found.
 *)
let chain extract =
   fchain extract;
   extract.ext_bchain extract

(************************************************************************
 * CREATION                                                             *
 ************************************************************************)

(*
 * Cache has empty lists.
 *)
let new_cache () =
    { cache_finfo = []; cache_binfo = [] }

(************************************************************************
 * EXTRACT CONSTRUCTION                                                 *
 ************************************************************************)

(*
 * Forward chaining rule.
 *)
let compute_wild t =
   let rec aux i = function
      h::t ->
         let terms, wildi, wilds = aux (i + 1) t in
            if is_var_term h then
               terms, i::wildi, h::wilds
            else
               h::terms, wildi, wilds
    | [] ->
         [], [], []
   in
   let terms, wildi, wilds = aux 0 t in
   let terms' = List.rev terms in
   let wilds' =
      if wilds = [] then
         None
      else
         Some (List.rev wildi, term_rewrite ([||], [||]) terms' (List.rev wilds))
   in
      terms', wilds'
      
let add_frule { cache_finfo = finfo; cache_binfo = binfo }
    { fc_ants = ants; fc_concl = concl; fc_just = just } =
   let args, wild = compute_wild ants in
   let info =
      { finfo_plates = List.map compute_template args;
        finfo_wild = wild;
        finfo_rw = term_rewrite ([||], [||]) args concl;
        finfo_just = just
      }
   in
      { cache_finfo = info::finfo; cache_binfo = binfo }

(*
 * Flatten the antecedents for rewriting.
 *)
let rec flatten_ants = function
   (l, t)::tl ->
      l @ [t] @ (flatten_ants tl)
 | [] ->
      []

(*
 * Inverse flatten a term list into an antecedent list.
 *)
let rec simple_ants = function
   ([], _)::tl -> simple_ants tl
 | (_::_, _)::_ -> false
 | [] -> true

let compute_spread_ants ants =
   if simple_ants ants then
      List.map (function x -> [], x)
   else
      let aux (l, _) = List.length l in
      let indices = List.map aux ants in
      let rec aux l = function
         i::t ->
            begin
               if i = 0 then
                  match l with
                     h::t' -> ([], h)::(aux t' t)
                   | [] -> raise (Invalid_argument "spread_ants")
               else
                  match List_util.split_list i l with
                     ants, h::t' -> (ants, h)::(aux t' t)
                   | _, [] -> raise (Invalid_argument "spread_ants")
            end
       | [] ->
            []
      in
      let spread_ants l =
         aux l indices
      in
         spread_ants

(*
 * Add a rule for backward chaining.
 *)
let add_brule  { cache_finfo = finfo; cache_binfo = binfo }
    { bc_concl = concl; bc_ants = ants; bc_just = just } =
   (* Flatten the antecedents *)
   let flat_ants = flatten_ants ants in
   let rw = term_rewrite ([||], [||]) [concl] flat_ants in
   let spread_ants = compute_spread_ants ants in
   let trw t =
      let values, _ = apply_rewrite rw ([||], [||]) [t] in
         spread_ants values
   in
   let info =
      { binfo_plate = compute_template concl;
        binfo_rw = trw;
        binfo_just = just
      }
   in
      { cache_finfo = finfo; cache_binfo = info::binfo }

(*
 * Build the forward chaining hash table.
 *)
let insert_ftable_entry tbl info =
   let rec aux i = function
      h::t ->
         fset_entry tbl h (i, info);
         aux (i + 1) t
    | [] ->
         ()
   in
      aux 0 info.finfo_plates

let make_ftable cache =
   let tbl = Hashtbl.create 97 in
      List.iter (insert_ftable_entry tbl) cache;
      tbl

(*
 * Build the backward chaining hash table.
 *)
let make_btable cache =
   let tbl = Hashtbl.create 97 in
      List.iter (bset_entry tbl) cache;
      tbl

(*
 * A default rule table.
 *)
let make_rules info =
   let tbl = Hashtbl.create 97 in
      List.iter (init_insts tbl) info;
      tbl

(*
 * Construct the extract.
 *)
let extract { cache_finfo = finfo; cache_binfo = binfo } =
   let node, goals, bchain = new_goals Empty None in
      {  (* Hyps *)
         ext_used = [];
         ext_hcount = 0;
         ext_names = [];
         ext_gnames = [];
         ext_hyps = [];
      
         (* Back chaining *)
         ext_goal = None;
         ext_node = node;
         ext_goals = goals;
         ext_bchain = bchain;
                                  
         (* Current world *)
         ext_world = Empty;
      
         (* Chaining base *)
         ext_base =
            { (* Rule tables *)
               ext_ftable = make_ftable finfo;
               ext_btable = make_btable binfo;
               ext_terms = Hashtbl.create 97;
               ext_rules = make_rules finfo;

               (* Forward chaining *)
               ext_index = 0;
               ext_fqueue = [];
      
               (* Possible worlds *)
               ext_worlds = []
            }
      }

(************************************************************************
 * HYP OPERATIONS                                                       *
 ************************************************************************)

(*
 * Insert a new hyp.
 *)
let add_hyp
    ({ ext_used = used;
       ext_hcount = hcount;
       ext_names = names;
       ext_gnames = gnames;
       ext_hyps = hyps;
       ext_goal = goal;
       ext_world = world;
       ext_base = base
     } as extract) i gname t =
   (* Have we already explored this world? *) 
   let t' = subst t (List.map mk_var_term names) gnames in
   let hash = compute_template t' in
   let i' = hcount - i - 1 in
      match find_world_extension extract world t' hash with
         Some world' ->
            (* Found an instance of the world *)
            let node, goals, bchain = new_goals world' goal in
               { ext_used = used;
                 ext_hcount = hcount + 1;
                 ext_names = List_util.insert_nth i' (name_of_world world') names;
                 ext_gnames = List_util.insert_nth i' gname gnames;
                 ext_hyps = List_util.insert_nth i' world' hyps;
                 ext_goal = goal;
                 ext_node = node;
                 ext_goals = goals;
                 ext_bchain = bchain;
                 ext_world = world';
                 ext_base = base
               }

       | None ->
            (* Construct a new world *)
            let name = mk_var_name extract in
            let rec inf =
               { inf_name = name;
                 inf_value = t';
                 inf_hash = hash;
                 inf_info = Hyp { hyp_world = world' }
               }
            and world' =
               Hypothesis { world_hyp = inf;
                            world_prev = world;
                            world_infs = [inf]
               }
            in
            let node, goals, bchain = new_goals world' goal in
               { ext_used = used;
                 ext_hcount = hcount + 1;
                 ext_names = List_util.insert_nth i' name names;
                 ext_gnames = List_util.insert_nth i' gname gnames;
                 ext_hyps = List_util.insert_nth i' world' hyps;
                 ext_goal = goal;
                 ext_node = node;
                 ext_goals = goals;
                 ext_bchain = bchain;
                 ext_world = world';
                 ext_base = base
               }

(*
 * Delete a hyp and all the hyps after it.
 * Also remove all subsequent hyps.  This won't actually be used
 * very much, since "backout" is usually performed by using
 * a different copy of the extract.  However, explicit backout
 * occurs during thinning.
 *)
let del_hyp
    { ext_used = used;
      ext_hcount = hcount;
      ext_names = names;
      ext_gnames = gnames;
      ext_hyps = hyps;
      ext_goal = goal;
      ext_base = base
    } i =
   if i = 0 then
      (* Remove all hyps *)
      let world = Empty in
      let node, goals, bchain = new_goals world goal in
         { ext_used = [];
           ext_hcount = 0;
           ext_names = [];
           ext_gnames = [];
           ext_hyps = [];
           ext_goal = goal;
           ext_node = node;
           ext_world = world;
           ext_goals = goals;
           ext_bchain = bchain;
           ext_base = base
         }
   else
      (* Find a specific hyp *)
      let i' = hcount - i in
      let rm, hyps' = List_util.split_list i' hyps in
      let world = List.hd hyps' in
      let node, goals, bchain = new_goals world goal in
      let extract =
         { ext_used = List_util.subtractq used rm;
           ext_hcount = i;
           ext_names = List_util.nth_tl i' names;
           ext_gnames = List_util.nth_tl i' gnames;
           ext_hyps = hyps';
           ext_goal = goal;
           ext_node = node;
           ext_goals = goals;
           ext_bchain = bchain;
           ext_world = world;
           ext_base = base
         }
      in
         extract

(*
 * Reference a particular hyp.
 *)
let ref_hyp ({ ext_hcount = hcount;
               ext_hyps = hyps;
               ext_used = used
             } as extract) i = 
   let hyp = List.nth hyps (hcount - i - 1) in
      if List.memq hyp used then
         extract
      else
         set_used extract (hyp::used)

(*
 * Rename a particular hyp.
 *)
let name_hyp ({ ext_hcount = hcount;
                ext_gnames = gnames
              } as extract) i gname =
   set_gnames extract (List_util.replace_nth (hcount - i - 1) gname gnames)

(************************************************************************
 * CONCL OPERATIONS                                                     *
 ************************************************************************)

(*
 * Choose a new conclusion.
 * This also resets the backward chaining queue
 * to be only those goals that the current goal depends upon.
 *)
let set_goal ({ ext_used = used;
                ext_hcount = hcount;
                ext_names = names;
                ext_gnames = gnames;
                ext_hyps = hyps;
                ext_world = world;
                ext_base = base
              } as extract) t =
   let t' = subst t (List.map mk_var_term names) gnames in
   let hash = compute_template t' in
   let goal =
      let goal' =
         { goal_goal = t';
           goal_hash = hash;
           goal_assums = [];
           goal_subgoals = Unexplored
         }
      in
         Some (try find_goal extract goal' with
                  Not_found ->
                     set_goal extract goal';
                     goal')
   in
   let node, goals, bchain = new_goals world goal in
      { ext_used = used;
        ext_hcount = hcount;
        ext_names = names;
        ext_gnames = gnames;
        ext_hyps = hyps;
        ext_world = world;
        ext_goal = goal;
        ext_node = node;
        ext_goals = goals;
        ext_bchain = bchain;
        ext_base = base
      }

                       
(************************************************************************
 * LOOKUP                                                               *
 ************************************************************************)

(*
 * We use this data structure to record the hyps that
 * are available at during the proof.  This would really
 * be a list of inferences, except for some of the results
 * produced by forward chaining, we don't know the particular
 * inference.  Se we settle for the root and index.
 *
 * This is mutable because we want to be able to
 * upgrade Root to Inf in place if it comes along.
 *)
type 'a hyp =
   Root of int * 'a inferenceInfo
 | Inf of 'a inference

type 'a hypref =
   { mutable hyp_info : 'a hyp }

type 'a hyplist =
   { hyp_count : int;
     hyp_hyps : 'a hypref list
   }

(*
 * Produce the initial hyp list from the list of worlds in the extract.
 *)
let init_hyps { ext_hcount = hcount; ext_hyps = hyps } =
   let aux = function
      Hypothesis { world_hyp = inf } ->
         { hyp_info = Inf inf }
    | Empty ->
         raise (Invalid_argument "init_hyps")
   in
      { hyp_count = hcount; hyp_hyps = List.map aux hyps }

(*
 * See of the hyp list contains an inference.
 * First check if the inference exists directly.
 * If that doesn't work, the check if the root for
 * the inference exists, and replace the reference
 * with the inf.
 *)
let hyp_index { hyp_count = hcount; hyp_hyps = hyps } =
   let search_root inf =
      match inf with
         { inf_value = t; inf_info = Inference ({ inf_values = values } as info) } ->
            let index = List_util.find_indexq t values in
            let rec search i = function
               ({ hyp_info = Root (j, info') } as hyp)::htl ->
                  if info == info' & j = index then
                     begin
                        hyp.hyp_info <- Inf inf;
                        Some i
                     end
                  else
                     search (i - 1) htl
             | _::htl ->
                  search (i - 1) htl
             | [] ->
                  None
            in
               search (hcount - 1) hyps
       | _ ->
            None
   in
   let search_inf inf =
      let rec search i = function
         { hyp_info = Inf inf' }::htl ->
            if inf' == inf then
               Some i
            else
               search (i - 1) htl
       | _::htl ->
            search (i - 1) htl
       | [] ->
            search_root inf
      in
         search (hcount - 1) hyps
   in
      search_inf

let hyp_index_force hyps inf =
   match hyp_index hyps inf with
      Some i -> i
    | None -> raise Not_found

(*
 * Add a rule as an inference.
 *)
let hyp_add_info { hyp_count = hcount; hyp_hyps = hyps }
    ({ inf_values = values } as info) =
   let rec aux i l = function
      _::t ->
         aux (i + 1) ({ hyp_info = Root (i, info) }::l) t
    | [] ->
         { hyp_count = hcount + i; hyp_hyps = l }
   in
      aux 0 hyps values
      
(*
 * Find the particular branch of the node that succeeded.
 *)
let find_and_branch { node_goal = { goal_subgoals = subgoals }; node_children = children } =
   match subgoals with
      Subgoals subgoals' ->
         let rec search = function
            (children::ctl), ({ sub_just = just }::gtl) ->
               let test { node_status = status } =
                  match status with
                     Primitive _ | Derived -> true
                   | Unproved | Unprovable | Derivable -> false
               in
                  if List.for_all test children then
                     children, just
                  else
                     search (ctl, gtl)
          | _ ->
               raise (Invalid_argument "find_and_branch")
         in
            search (children, subgoals')
    | Unexplored | Unsolvable ->
         raise (Invalid_argument "find_and_branch")

(*
 * Split the infs into those that can be inferred from the current world,
 * and those that must be postponed.
 *)
let split_infs infs world =
   let rec aux = function
      inf::tl ->
         let world' = world_of_inf inf in
         let ninfs, infs' = aux tl in
            if is_child world world' then
               inf::ninfs, infs'
            else
               ninfs, inf::infs'
    | [] ->
         [], []
   in
      aux infs

(*
 * To perform forward chaining given the hyp list,
 * keep inferring through roots.  Return the
 * justifications, as well as the new hyp list.
 *)
let rec forechain hyps = function
   inf::infs ->
      begin
         match hyp_index hyps inf with
            Some i ->
               forechain hyps infs
          | None ->
               (* Infer the inf *)
               match inf with
                  { inf_info = Inference ({ inf_just = just; inf_args = args } as info) } ->
                     let l, hyps' = forechain hyps args in
                     let indices = List.map (hyp_index_force hyps') args in
                     let hyps'' = hyp_add_info hyps' info in
                     let l', hyps''' = forechain hyps'' infs in
                        l @ ((indices, just)::l), hyps'''
                | { inf_info = Hyp _ } ->
                     failwith "forechain: hyp_error"
      end
         
 | [] ->
      [], hyps

(*
 * Backchain from a node, given a collection of infs that
 * must be inferred.  Infer them as soon as possible.
 *)
let rec backchain hyps infs
    ({ node_status = status;
       node_world = world
     } as node) =
   let ninfs, infs' = split_infs infs world in
   let fjust, hyps' = forechain hyps ninfs in
   let children', just = find_and_branch node in
   let bproof = BackTactic (just, List.map (backchain hyps' infs') children') in
   let proof =
      if fjust = [] then
         bproof
      else
         SeqTactic [ForeTactics fjust; bproof]
   in
      proof
      
(*
 * Derive the backchain tree, and collect the inferences that
 * must be satisfied by forward chaining.
 *)
let collect_infs node =
   let rec search l ({ node_status = status } as node) =
      match status with
         Primitive inf -> inf::l
       | Derived ->
            let children', _ = find_and_branch node in
               List.fold_left search l children'
       | Unproved | Unprovable | Derivable ->
            raise (Invalid_argument "collect")
   in
      search [] node
 
(*
 * Produce a proof of the goal in the current world.
 * This will be a combination of forward and backward chaining.
 * Assume that there is a proof.
 *
 * This is complicated by the fact that we want
 * to perform forward chaining as soon as possible.
 * For this purpose, we erform two passes:
 *    In the first pass, we collect all the inferences that
 *    should be infered.
 *
 *    In the second pass, we combine the forward,
 *    backward chaining.
 *)
let lookup ({ ext_node = node } as extract) =
   match node with
      Some node' ->
         let hyps = init_hyps extract in
         let infs = collect_infs node' in
            backchain hyps infs node'
    | None ->
         raise (Invalid_argument "lookup")

(************************************************************************
 * SYNTHESIS                                                            *
 ************************************************************************)

(*
 * Find the handles of the hyps being used.
 *)
let synthesize ({ ext_used = used } as extract) syns =
   let rec combine = function
      { syn_used = used' }::t ->
         List_util.unionq used (combine t)
    | [] ->
         used
   in
      { syn_extract = extract; syn_used = combine syns }

(*
 * Get the used hyp numbers.
 *)
let used_hyps
    { syn_extract = { ext_hyps = hyps; ext_hcount = hcount };
      syn_used = used
    } =
   List.map (function inf -> hcount - (List_util.find_indexq inf hyps) - 1) used
   
(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
