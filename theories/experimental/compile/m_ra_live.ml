(*
 * Generate the live sets for abstract assembly instructions.
 *
 * ----------------------------------------------------------------
 *
 * Copyright (C) 2002 Jason Hickey, Caltech
 * Copyright (C) 2002 Justin David Smith, Caltech
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
extends M_ra_type
extends M_ra_state

open Format

open Lm_debug
open Lm_trace
open Lm_symbol
open Lm_symbol_matrix

open M_ra_type
open M_ra_state

(*
 * A set-like structure that keeps track of the length of
 * the live range of a variable.
 *)
module type LiveSetSig =
sig
   type t

   val empty : t
   val subtract_defs : t -> SymbolSet.t -> t
   val add_uses : t -> SymbolSet.t -> t
   val union : t -> t -> t
   val equal : t -> t -> bool
   val add : t -> int -> t
   val to_set : t -> SymbolSet.t

   val find : t -> symbol -> int
   val remove : t -> symbol -> t

   val iter : (symbol -> int -> unit) -> t -> unit
   val fold : ('a -> symbol -> int -> 'a) -> 'a -> t -> 'a
end

module LiveSet : LiveSetSig =
struct
   type t = int SymbolTable.t

   let empty = SymbolTable.empty

   let subtract_defs length defs =
      SymbolSet.fold SymbolTable.remove length defs

   let add_uses length uses =
      SymbolSet.fold (fun length v ->
            SymbolTable.filter_add length v (function
               Some i -> i
             | None -> 1)) length uses

   let union length1 length2 =
      SymbolTable.fold (fun length v i ->
            SymbolTable.filter_add length v (function
               Some j -> max i j
             | None -> i)) length1 length2

   let add length depth =
      SymbolTable.map (fun i -> i + depth) length

   let equal length1 length2 =
      if SymbolTable.cardinal length1 = SymbolTable.cardinal length2 then
         try
            SymbolTable.iter (fun v i ->
                  let j = SymbolTable.find length2 v in
                     if i <> j then
                        raise Not_found) length1;
            true
         with
            Not_found ->
               false
      else
         false

   let to_set live =
      SymbolTable.fold (fun set v _ ->
            SymbolSet.add set v) SymbolSet.empty live

   let iter = SymbolTable.iter
   let fold = SymbolTable.fold
   let find = SymbolTable.find
   let remove = SymbolTable.remove
end

(*
 * Liveness analysis.
 *)
module MakeLive (Frame : FrameSig) : LiveSig
   with type 'a block = 'a Frame.block
   with type inst = Frame.inst =
struct
   (***  Types  ***)


   (*
    * A program is a list of blocks.
    *)
   type 'a block = 'a Frame.block
   type inst = Frame.inst


   (*
    * A basic block contains a sequence of assembly instructions.  It
    * begins with a label, ends with a jump, and contains no other labels.
    * We use faster algorithms for computing defs/uses on basic blocks.
    *)
   type 'inst live_block =
      { (* Save all the block info *)
        block_label  : label;
        block_code   : 'inst code;

        (* Defs and uses *)
        block_defs   : (int * label * SymbolSet.t) list;
        block_uses   : LiveSet.t;

        (* Dataflow *)
        block_in     : LiveSet.t;

        (* Remember the original block *)
        block_block  : inst Frame.block
      }


   (*
    * Type used for the environment of live_block structures,
    * indexed on the block labels.
    *)
   type benv = inst live_block SymbolTable.t


   (*
    * Lookup a value from the classification table.
    *)
   let cenv_lookup cenv v =
      try SymbolTable.find cenv v with
         Not_found ->
            raise (Invalid_argument ("liveness: unclassified var: " ^ string_of_symbol v))


   (***  Control Flow Graph  ***)


   (*
    * Get the block liveness.  Some destinations won't exist (like the
    * seg_fault handler).  Assume those destinations have no uses.
    *)
   let block_live blocks label =
      try (SymbolTable.find blocks label).block_in with
         Not_found ->
            LiveSet.empty


   (*
    * Compute the defs/uses in a basic block.  The defs are the union
    * of all the defined values, captured at the branch points.
    *)
   let block_defs code =
      let rec collect depth defs dtable code =
         let { code_dst = defs';
               code_class = cclass;
               code_rest = rest
             } = code
         in
         let defs = SymbolSet.union defs defs' in
         let dtables =
            match cclass with
               CodeJump label ->
                  (depth, label, defs) :: dtable
             | CodeNormal
             | CodeMove ->
                  dtable
         in
            List.fold_left (collect (succ depth) defs) dtable rest
      in
         collect 0 SymbolSet.empty [] code


   (*
    * The uses are computed by propagating backward, subtracting defs.
    *)
   let block_uses code =
      let rec collect uses'' code =
         let { code_dst = defs;
               code_src = uses;
               code_rest = rest
             } = code
        in
        let uses' = List.fold_left collect LiveSet.empty rest in
        let uses' = LiveSet.subtract_defs uses' defs in
        let uses' = LiveSet.add uses' 1 in
        let uses' = LiveSet.add_uses uses' uses in
           LiveSet.union uses'' uses'
      in
         collect LiveSet.empty code


   (*
    * Build a block from the assembly instruction list.
    * The first instruction should be a label, and there
    * should be no jumps except for the last instruction.
    *)
   let basic_block ignore block =
      let label = Frame.block_label block in
      let code  = Frame.block_code ignore block in
      let defs  = block_defs code in
      let uses  = block_uses code in
         { block_label = label;
           block_code  = code;
           block_defs  = defs;
           block_uses  = uses;
           block_in    = uses;
           block_block = block
         }


   (***  Block Dataflow Graph  ***)


   (*
    * Compute the least-fixed point of the dataflow equations:
    *     in[n] = uses[n] + (out[n] - defs[n])
    *     out[n] = union s in succ[n]. in[n]
    *
    * The dataflow equations are monotone, and the size of the sets
    * is limited by the total number of vars in the program,
    * so we can calculate the least-fixed point by iteration
    * (and be sure of termination).
    *
    * The input includes the control-flow graph,
    * a table that maps nodes to basic blocks,
    * and a set of nodes.
    *)
   let dataflow benv labels =
      (*
       * Compute the dataflow assignment for a single node.
       * Returns true iff the live sets have changed.
       *)
      let rec update_block updated benv label =
         let block =
            try SymbolTable.find benv label with
               Not_found -> raise (Invalid_argument "dataflow")
         in
         let { block_in = live;
               block_uses = uses;
               block_defs = defs
             } = block
         in
         let live' =
            List.fold_left (fun live (depth, label, defs) ->
                  let live' = block_live benv label in
                  let live' = LiveSet.subtract_defs live' defs in
                  let live' = LiveSet.add live' depth in
                     LiveSet.union live live') uses defs
         in
            if LiveSet.equal live live' then
               updated, benv
            else
               let block = { block with block_in = live' } in
               let benv = SymbolTable.add benv label block in
                  true, benv
      in

      (* Compute the fixpoint *)
      let rec fixpoint benv =
         let rec fixpoint_list benv updated l =
            match l with
               h :: t ->
                  let updated, benv = fixpoint_list benv updated t in
                     fixpoint_elem benv updated h
             | [] ->
                  updated, benv
         and fixpoint_elem benv updated e =
            match e with
               Elem label ->
                  update_block updated benv label
             | Lm_trace (x, l) ->
                  fixpoint_list benv updated (Elem x :: l)
         in
         let flag, benv = fixpoint_list benv false labels in
            if flag then
               fixpoint benv
            else
               benv
      in
         fixpoint benv


   (***  Interference Graph  ***)


   (*
    * Def statistics.
    *)
   let add_depth defs depth =
      let len = Array.length defs in
      let defs =
         if depth < len then
            defs
         else
            let defs' = Array.create (succ depth) 0 in
               Array.blit defs 0 defs' 0 len;
               defs'
      in
         defs.(depth) <- succ defs.(depth);
         defs


   let stats_add get set graph depth v =
      let stats =
         try SymbolTable.find graph.igraph_stats v with
            Not_found ->
               raise (Invalid_argument ("graph_add: " ^ string_of_symbol v))
      in
      let defs = get stats in
      let len = Array.length defs in
      let defs =
         if depth < len then
            defs
         else
            let defs' = Array.create (succ depth) 0 in
               Array.blit defs 0 defs' 0 len;
               set stats defs';
               defs'
      in
         defs.(depth) <- succ defs.(depth)


   let stats_add_length graph v i =
      let stats =
         try SymbolTable.find graph.igraph_stats v with
            Not_found ->
               raise (Invalid_argument ("graph_add: " ^ string_of_symbol v))
      in
         stats.stats_length <- min stats.stats_length i


   let stats_add_defs graph depth defs live =
      SymbolSet.iter (fun v ->
            let length =
               try LiveSet.find live v with
                  Not_found ->
                     0
            in
               stats_add (**)
                  (fun stats -> stats.stats_defs)
                  (fun stats defs -> stats.stats_defs <- defs)
                  graph depth v;
            stats_add_length graph v length) defs

   let stats_add_uses graph depth uses =
      SymbolSet.iter (fun v ->
            stats_add (**)
               (fun stats -> stats.stats_uses)
               (fun stats uses -> stats.stats_uses <- uses)
               graph
               depth
               v) uses


   (*
    * Interferance graph operations.  For a normal instruction, all the defs
    * interfere with all the live vars.  Only add interferences within a
    * register class.
    *)
   let graph_add_normal cenv graph depth defs uses live =
      let igraph = graph.igraph_graph in
         stats_add_defs graph depth defs live;
         stats_add_uses graph depth uses;
         SymbolSet.iter (fun v1 ->
               let (rc1 : int) = cenv_lookup cenv v1 in
                  LiveSet.iter (fun v2 _ ->
                        let (rc2 : int) = cenv_lookup cenv v2 in
                           if rc1 = rc2 && not (Lm_symbol.eq v1 v2) then
                              SymSymbolMatrix.add igraph v1 v2 true) live) defs


   (*
    * New move stats.
    *)
   let move_new_stats depth =
      let depth' = Array.create (succ depth) 0 in
         depth'.(depth) <- 1;
         { move_depth = depth' }


   (*
    * Add the stats to an existing move stat table.
    *)
   let move_add_stats stats depth =
      let { move_depth = depth' } = stats in
         { move_depth = add_depth depth' depth }


   (*
    * Add a move.
    *)
   let stats_add_move graph def use depth =
      AsymSymbolMatrix.filter_add graph.igraph_moves def use (fun stats ->
            match stats with
               Some stats ->
                  move_add_stats stats depth
             | None ->
                  move_new_stats depth)


   (*
    * Moves are special: the defs should be a single variable.
    * The def _does not_ interfere with its uses.
    *)
   let graph_add_move cenv graph depth defs uses live =
      let igraph = graph.igraph_graph in
      let def = SymbolSet.choose defs in
      let use = SymbolSet.choose uses in
      let (rc1 : int) = cenv_lookup cenv def in
      let (rc2 : int) = cenv_lookup cenv use in
      let _ =
         if rc1 <> rc2 then
            raise (Invalid_argument (**)
                      (Printf.sprintf "graph_add_move: cenv for def, use disagree: def %s = %d, use %s = %d" (**)
                          (string_of_symbol def) rc1 (string_of_symbol use) rc2))
      in
         (* Add interference edges *)
         LiveSet.iter (fun v _ ->
               let (rc2 : int) = cenv_lookup cenv v in
                  if rc1 = rc2 && not (Lm_symbol.eq v def) && not (Lm_symbol.eq v use) then
                     SymSymbolMatrix.add igraph def v true) live;

         (* Add move stats *)
         stats_add_defs graph depth defs live;
         stats_add_uses graph depth uses;
         stats_add_move graph def use depth


   (*
    * Update the interference graph for the instructions within
    * the block.  The live edges are computed from last to first
    * in the instruction order.  Whenever we encounter a jump,
    * we add live_in from the destination.  This builds the graph
    * alone, no live blocks are created.
    *)
   let block_dataflow_graph cenv graph benv depth label =
      let block =
         try SymbolTable.find benv label with
            Not_found ->
               raise (Invalid_argument "block_dataflow_graph")
      in
      let rec collect live' code =
         let { code_src = uses;
               code_dst = defs;
               code_class = cclass;
               code_inst = inst;
               code_rest = rest
             } = code
         in
         let live = List.fold_left collect LiveSet.empty rest in
         let live =
            match cclass with
               CodeNormal ->
                  graph_add_normal cenv graph depth defs uses live;
                  live
             | CodeMove ->
                  graph_add_move cenv graph depth defs uses live;
                  live
             | CodeJump label ->
                  let live = LiveSet.union live (block_live benv label) in
                     graph_add_normal cenv graph depth defs uses live;
                     live
         in
         let live = LiveSet.subtract_defs live defs in
         let live = LiveSet.add_uses live uses in
         let live = LiveSet.add live 1 in
            LiveSet.union live' live
      in
         ignore (collect LiveSet.empty block.block_code)


   (*
    * This is just like creating the dataflow graph,
    * but we create liveness information for the instructions
    * instead.
    *)
   let block_dataflow_live benv depth label =
      let block =
         try SymbolTable.find benv label with
            Not_found ->
               raise (Invalid_argument "block_dataflow_live")
      in
      let rec collect live' code =
         let { code_src   = uses;
               code_dst   = defs;
               code_class = cclass;
               code_inst  = inst;
               code_rest  = rest
             } = code
         in
         let live, rest =
            List.fold_left (fun (live, rest) code ->
                  let live, code = collect live code in
                  let rest = code :: rest in
                     live, rest) (LiveSet.empty, []) rest
         in
         let rest = List.rev rest in
         let live, inst =
            match cclass with
               CodeNormal
             | CodeMove ->
                  let inst =
                     { live_src = uses;
                       live_dst = defs;
                       live_out = LiveSet.to_set live;
                       live_class = cclass;
                       live_depth = depth;
                       live_inst = inst;
                       live_rest = rest
                     }
                  in
                  let live = LiveSet.subtract_defs live defs in
                  let live = LiveSet.add_uses live uses in
                     live, inst
             | CodeJump label ->
                  let live = LiveSet.union live (block_live benv label) in
                  let inst =
                     { live_src = uses;
                       live_dst = defs;
                       live_out = LiveSet.to_set live;
                       live_class = cclass;
                       live_depth = depth;
                       live_inst = inst;
                       live_rest = rest
                     }
                  in
                  let live = LiveSet.subtract_defs live defs in
                  let live = LiveSet.add_uses live uses in
                     live, inst
         in
         let live = LiveSet.add live 1 in
         let live = LiveSet.union live' live in
            live, inst
      in
      let _, code = collect LiveSet.empty block.block_code in
         Frame.block_live block.block_block code


   (*
    * Build the interference graph from all the blocks.
    *)
   let build_igraph cenv benv labels =
      let size = SymbolTable.cardinal cenv in
      let graph =
         { igraph_stats =
              SymbolTable.map (fun _ ->
                    { stats_length = 10000; stats_defs = [||]; stats_uses = [||] }) cenv;
           igraph_graph = SymSymbolMatrix.create size;
           igraph_moves = AsymSymbolMatrix.create size
         }
      in
         Lm_trace.iter_depth (block_dataflow_graph cenv graph benv) labels;
         if debug debug_live then
            begin
               eprintf "@[<hv 3>Interference graph:";
               SymSymbolMatrix.iter (fun v1 v2 _ ->
                     eprintf "@ %a <--> %a" pp_print_symbol v1 pp_print_symbol v2) graph.igraph_graph;
               eprintf "@]@."
            end;
         graph


   (*
    * Build the interference graph from all the blocks.
    *)
   let build_live cenv benv labels =
      Lm_trace.map_depth (block_dataflow_live benv) labels


   (***  Global Interface  ***)


   (*
    * Builds the benv: computes the dataflow between blocks.
    * To calculate liveness:
    *    1. create the blocks
    *    2. perform block dataflow
    *    3. map dataflow through the blocks
    *)
   let create_aux ignore blocks =
      (* Convert all the blocks, and put them in a table *)
      let blocks = Lm_trace.map (basic_block ignore) blocks in
      let benv =
         Lm_trace.fold (fun benv block ->
               SymbolTable.add benv block.block_label block) SymbolTable.empty blocks
      in

      (* Reduce the block trace to a label trace *)
      let labels = Lm_trace.map (fun block -> block.block_label) blocks in

      (* Perform dataflow *)
      let benv = dataflow benv labels in
         benv, labels


   (*
    * Create an interference graph, for use by register allocation.
    *)
   let create_graph cenv ignore blocks =
      let benv, labels = create_aux ignore blocks in
         build_igraph cenv benv labels


   (*
    * Create a trace of live inst blocks.  This is a one-pass algorithm.
    * You may find the next two functions, for a two-pass algorithm, to
    * be more efficient.  This function always gets depths right; the next
    * two functions rely on the user to specify proper depths.
    *)
   let create_live cenv ignore blocks =
      let benv, labels = create_aux ignore blocks in
      let blocks = build_live cenv benv labels in
         if debug debug_live then
            Frame.pp_print_live_blocks err_formatter blocks;
         blocks


   (*
    * Create a benv for block-by-block construction of live information.
    * This is used by algorithms which can afford to compute liveness
    * information on blocks ``on demand''; by not precomputing everything,
    * we save a bit of memory and some thrashing (and some real compute
    * time if the algorithm does not require liveness information on all
    * blocks).
    *
    * This returns the ``benv'', which contains dataflow info (but has not
    * computed liveness information for individual insts).  Pass the benv
    * to create_live_block, with the block label of interest, to build the
    * final (inst live block) structure.
    *)
   let create_live_benv ignore blocks =
      let benv, _ = create_aux ignore blocks in
         benv


   (*
    * Create a live block, based on benv information that was previously
    * computed.  This is slightly more efficient than calling create_live,
    * since we only compute the data structures on demand (as opposed to
    * preallocating everything).
    *
    * Typically, you would do Lm_trace.map_depth over the blocks of interest
    * to call this; if you really don't care about depth, then you can do
    * Lm_trace.map and give 0 here.
    *)
   let create_live_block benv depth label =
      block_dataflow_live benv depth label
end (* struct *)
