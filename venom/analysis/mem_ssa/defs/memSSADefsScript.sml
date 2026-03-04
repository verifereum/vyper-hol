(*
 * Memory SSA Analysis — Definitions
 *
 * Ported from vyper/venom/analysis/mem_ssa.py.
 * LLVM-style Memory SSA: tracks memory state versions, not partitioned
 * ranges.  Each store creates a new version (MemDef), each load reads
 * a version (MemUse), join points get MemPhi nodes.
 *
 * TOP-LEVEL:
 *   mssa_node, mssa_state    — types
 *   mssa_build               — construct memory SSA for a function
 *   mssa_get_memory_def      — instruction → def access id
 *   mssa_get_memory_use      — instruction → use access id
 *   mssa_get_exit_def        — block → last reaching definition
 *   mssa_get_clobbered       — walk for clobbering definition
 *   mssa_get_aliased         — walk for aliased accesses
 *   mssa_mark_volatile       — mark a location volatile
 *   memory_ssa_analyze, storage_ssa_analyze, transient_ssa_analyze
 *
 * Helper (internal):
 *   mn_inst_id, mn_block, mn_loc — node projections
 *   mssa_process_inst, mssa_process_block, mssa_process_blocks — Phase 1
 *   mssa_insert_phis — Phase 2
 *   mssa_connect_all — Phase 3
 *   mssa_remove_redundant_phis — Phase 4
 *   find_prev_def — backward scan within block
 *
 * Divergences from Python:
 *   - Flat map representation: nodes stored in (num, mssa_node) fmap
 *   - LiveOnEntry is access_id 0 (sentinel, not stored in ms_nodes)
 *   - reaching_def stored in separate ms_reaching map (not embedded in node)
 *   - Uses fuel for recursive functions (get_exit_def, clobber walk)
 *)

Theory memSSADefs
Ancestors
  memAliasDefs dominatorDefs
Libs
  listTheory finite_mapTheory pairTheory

(* ==========================================================================
   Types
   ========================================================================== *)

(* A memory SSA node.  Each node carries the originating instruction's id,
   the block it belongs to, and the memory location accessed.
   MnPhi carries only the block label (no instruction). *)
Datatype:
  mssa_node =
    MnDef num string mem_loc     (* inst_id, block_label, location *)
  | MnUse num string mem_loc     (* inst_id, block_label, location *)
  | MnPhi string                 (* block_label *)
End

(* Memory SSA analysis result.
 * access_id = 0 is the implicit LiveOnEntry sentinel. *)
Datatype:
  mssa_state = <|
    ms_nodes      : (num, mssa_node) fmap;          (* access_id → node *)
    ms_reaching   : (num, num) fmap;                 (* access_id → reaching_def id *)
    ms_phi_ops    : (num, (num # string) list) fmap; (* phi_id → [(rd_id, pred_block)] *)
    ms_block_defs : (string, num list) fmap;         (* block → ordered def ids *)
    ms_block_uses : (string, num list) fmap;         (* block → ordered use ids *)
    ms_block_phis : (string, num) fmap;              (* block → phi id (at most one) *)
    ms_inst_def   : (num, num) fmap;                 (* inst_id → def access_id *)
    ms_inst_use   : (num, num) fmap;                 (* inst_id → use access_id *)
    ms_next_id    : num                              (* next fresh id *)
  |>
End

(* ==========================================================================
   Node projections
   ========================================================================== *)

Definition mn_inst_id_def:
  mn_inst_id (MnDef iid _ _) = iid ∧
  mn_inst_id (MnUse iid _ _) = iid ∧
  mn_inst_id (MnPhi _) = 0
End

Definition mn_block_def:
  mn_block (MnDef _ blk _) = blk ∧
  mn_block (MnUse _ blk _) = blk ∧
  mn_block (MnPhi blk) = blk
End

Definition mn_loc_def:
  mn_loc (MnDef _ _ loc) = loc ∧
  mn_loc (MnUse _ _ loc) = loc ∧
  mn_loc (MnPhi _) = ml_empty
End

(* ==========================================================================
   Initial state
   ========================================================================== *)

Definition mssa_init_def:
  mssa_init =
    <| ms_nodes      := FEMPTY;
       ms_reaching   := FEMPTY;
       ms_phi_ops    := FEMPTY;
       ms_block_defs := FEMPTY;
       ms_block_uses := FEMPTY;
       ms_block_phis := FEMPTY;
       ms_inst_def   := FEMPTY;
       ms_inst_use   := FEMPTY;
       ms_next_id    := 1  (* 0 reserved for LiveOnEntry *)
    |>
End

(* ==========================================================================
   Phase 1: Collect definitions and uses
   ========================================================================== *)

(* Process one instruction: create MnUse and/or MnDef if it accesses memory. *)
Definition mssa_process_inst_def:
  mssa_process_inst bp addr_sp blk_lbl ms inst =
    let rloc = bp_get_read_location bp inst addr_sp in
    let wloc = bp_get_write_location bp inst addr_sp in
    (* Create use if instruction reads memory *)
    let ms1 =
      if rloc = ml_empty then ms
      else
        let uid = ms.ms_next_id in
        let old = fmap_lookup_list ms.ms_block_uses blk_lbl in
        ms with <|
          ms_nodes      := ms.ms_nodes |+ (uid, MnUse inst.inst_id blk_lbl rloc);
          ms_block_uses := ms.ms_block_uses |+ (blk_lbl, SNOC uid old);
          ms_inst_use   := ms.ms_inst_use |+ (inst.inst_id, uid);
          ms_next_id    := uid + 1
        |>
    in
    (* Create def if instruction writes memory *)
    if wloc = ml_empty then ms1
    else
      let did = ms1.ms_next_id in
      let old = fmap_lookup_list ms1.ms_block_defs blk_lbl in
      ms1 with <|
        ms_nodes      := ms1.ms_nodes |+ (did, MnDef inst.inst_id blk_lbl wloc);
        ms_block_defs := ms1.ms_block_defs |+ (blk_lbl, SNOC did old);
        ms_inst_def   := ms1.ms_inst_def |+ (inst.inst_id, did);
        ms_next_id    := did + 1
      |>
End

(* Process all instructions in a basic block. *)
Definition mssa_process_block_def:
  mssa_process_block bp addr_sp blk_lbl ms [] = ms ∧
  mssa_process_block bp addr_sp blk_lbl ms (inst::insts) =
    mssa_process_block bp addr_sp blk_lbl
      (mssa_process_inst bp addr_sp blk_lbl ms inst) insts
End

(* Process blocks in DFS pre-order. *)
Definition mssa_process_blocks_def:
  mssa_process_blocks bp addr_sp fn ms [] = ms ∧
  mssa_process_blocks bp addr_sp fn ms (lbl::lbls) =
    case lookup_block lbl fn.fn_blocks of
      NONE => mssa_process_blocks bp addr_sp fn ms lbls
    | SOME bb =>
        mssa_process_blocks bp addr_sp fn
          (mssa_process_block bp addr_sp lbl ms bb.bb_instructions) lbls
End

(* ==========================================================================
   get_exit_def — last reaching definition at block exit (fuel-based)

   1. Last MemDef in block (if any)
   2. Block's MemPhi (if any)
   3. Recurse to idom
   4. LiveOnEntry (id 0)
   ========================================================================== *)

Definition mssa_get_exit_def_def:
  mssa_get_exit_def ms dom 0 lbl = 0 ∧
  mssa_get_exit_def ms dom (SUC fuel) lbl =
    let defs = fmap_lookup_list ms.ms_block_defs lbl in
    if defs ≠ [] then LAST defs
    else
      case FLOOKUP ms.ms_block_phis lbl of
        SOME phi_id => phi_id
      | NONE =>
          (case idom_of dom lbl of
             SOME idom_lbl => mssa_get_exit_def ms dom fuel idom_lbl
           | NONE => 0)
End

(* ==========================================================================
   Phase 2: Insert MemPhi nodes at dominance frontiers
   ========================================================================== *)

(* Insert a phi at a single frontier block (if not already present).
 * Returns (ms', T) if a new phi was inserted, (ms, F) otherwise. *)
Definition mssa_insert_phi_at_def:
  mssa_insert_phi_at ms cfg dom fuel blk_lbl =
    case FLOOKUP ms.ms_block_phis blk_lbl of
      SOME _ => (ms, F)
    | NONE =>
        let phi_id = ms.ms_next_id in
        let preds = cfg_preds_of cfg blk_lbl in
        let ops = MAP (λp. (mssa_get_exit_def ms dom fuel p, p)) preds in
        let ms' = ms with <|
          ms_nodes      := ms.ms_nodes |+ (phi_id, MnPhi blk_lbl);
          ms_block_phis := ms.ms_block_phis |+ (blk_lbl, phi_id);
          ms_phi_ops    := ms.ms_phi_ops |+ (phi_id, ops);
          ms_next_id    := phi_id + 1
        |> in
        (ms', T)
End

(* Process the dominance frontiers of one block.
 * Returns (ms', new_worklist_additions). *)
Definition mssa_process_frontiers_def:
  mssa_process_frontiers ms cfg dom fuel [] = (ms, []) ∧
  mssa_process_frontiers ms cfg dom fuel (f::fs) =
    let (ms1, inserted) = mssa_insert_phi_at ms cfg dom fuel f in
    let (ms2, rest) = mssa_process_frontiers ms1 cfg dom fuel fs in
    (ms2, if inserted then f :: rest else rest)
End

(* Worklist iteration for phi placement.
 * fuel bounds total iterations (at most |blocks| phis can be inserted). *)
Definition mssa_insert_phis_def:
  mssa_insert_phis ms cfg dom ef 0 wl = ms ∧
  mssa_insert_phis ms cfg dom ef (SUC fuel) [] = ms ∧
  mssa_insert_phis ms cfg dom ef (SUC fuel) (b::wl) =
    let frontiers = frontier_of dom b in
    let (ms', new_wl) = mssa_process_frontiers ms cfg dom ef frontiers in
    mssa_insert_phis ms' cfg dom ef fuel (wl ++ new_wl)
End

(* ==========================================================================
   Phase 3: Connect reaching definitions
   ========================================================================== *)

(* Find the last MemDef in a block's instruction list before a target inst.
 * Scans forward; returns the def closest to (but before) target_id. *)
Definition mssa_find_prev_def_def:
  mssa_find_prev_def ms [] target_id = NONE ∧
  mssa_find_prev_def ms (inst::insts) target_id =
    if inst.inst_id = target_id then NONE
    else
      case mssa_find_prev_def ms insts target_id of
        SOME d => SOME d
      | NONE => FLOOKUP ms.ms_inst_def inst.inst_id
End

(* Get the reaching definition for a def/use at a given position in a block.
 * 1. Scan backward in same block for preceding MemDef
 * 2. Check block's MemPhi
 * 3. Get exit_def from immediate dominator
 * 4. LiveOnEntry *)
Definition mssa_reaching_in_block_def:
  mssa_reaching_in_block ms dom fn fuel inst_id blk_lbl =
    case lookup_block blk_lbl fn.fn_blocks of
      NONE => 0
    | SOME bb =>
        case mssa_find_prev_def ms bb.bb_instructions inst_id of
          SOME def_id => def_id
        | NONE =>
            (case FLOOKUP ms.ms_block_phis blk_lbl of
               SOME phi_id => phi_id
             | NONE =>
                 (case idom_of dom blk_lbl of
                    SOME idom_lbl => mssa_get_exit_def ms dom fuel idom_lbl
                  | NONE => 0))
End

(* Connect a list of access ids to their reaching definitions. *)
Definition mssa_connect_list_def:
  mssa_connect_list ms dom fn fuel [] = ms ∧
  mssa_connect_list ms dom fn fuel (aid::aids) =
    case FLOOKUP ms.ms_nodes aid of
      NONE => mssa_connect_list ms dom fn fuel aids
    | SOME (MnPhi _) => mssa_connect_list ms dom fn fuel aids
    | SOME node =>
        let rd = mssa_reaching_in_block ms dom fn fuel
                   (mn_inst_id node) (mn_block node) in
        let ms' = ms with ms_reaching := ms.ms_reaching |+ (aid, rd) in
        mssa_connect_list ms' dom fn fuel aids
End

(* Connect all uses and defs across all blocks (in DFS pre-order). *)
Definition mssa_connect_all_def:
  mssa_connect_all ms dom fn fuel [] = ms ∧
  mssa_connect_all ms dom fn fuel (lbl::lbls) =
    let uses = fmap_lookup_list ms.ms_block_uses lbl in
    let defs = fmap_lookup_list ms.ms_block_defs lbl in
    let ms1 = mssa_connect_list ms dom fn fuel uses in
    let ms2 = mssa_connect_list ms1 dom fn fuel defs in
    mssa_connect_all ms2 dom fn fuel lbls
End

(* ==========================================================================
   Phase 4: Remove redundant phi nodes
   ========================================================================== *)

(* A phi is redundant if all operands have the same reaching-def id. *)
Definition mssa_phi_redundant_def:
  mssa_phi_redundant [] = T ∧
  mssa_phi_redundant ((first_rd, _) :: rest) =
    EVERY (λ(rd, _). rd = first_rd) rest
End

(* Remove all redundant phis.  Input: list of (block_label, phi_id) pairs. *)
Definition mssa_remove_redundant_phis_def:
  mssa_remove_redundant_phis ms [] = ms ∧
  mssa_remove_redundant_phis ms ((lbl, phi_id)::rest) =
    case FLOOKUP ms.ms_phi_ops phi_id of
      NONE => mssa_remove_redundant_phis ms rest
    | SOME ops =>
        if mssa_phi_redundant ops then
          mssa_remove_redundant_phis
            (ms with ms_block_phis := ms.ms_block_phis \\ lbl) rest
        else
          mssa_remove_redundant_phis ms rest
End

(* ==========================================================================
   Top-level construction
   ========================================================================== *)

Definition mssa_build_def:
  mssa_build cfg dom bp fn addr_sp =
    let order = cfg.cfg_dfs_pre in
    let fuel = LENGTH (fn_labels fn) in
    (* Phase 1: collect defs and uses *)
    let ms = mssa_process_blocks bp addr_sp fn mssa_init order in
    (* Phase 2: insert phi nodes *)
    let def_blocks = MAP FST (fmap_to_alist ms.ms_block_defs) in
    let ms = mssa_insert_phis ms cfg dom fuel (fuel * fuel) def_blocks in
    (* Phase 3: connect reaching definitions *)
    let ms = mssa_connect_all ms dom fn fuel order in
    (* Phase 4: remove redundant phis *)
    let phi_pairs = fmap_to_alist ms.ms_block_phis in
    mssa_remove_redundant_phis ms phi_pairs
End

(* ==========================================================================
   Query: get_memory_def / get_memory_use
   ========================================================================== *)

Definition mssa_get_memory_def_def:
  mssa_get_memory_def ms inst_id = FLOOKUP ms.ms_inst_def inst_id
End

Definition mssa_get_memory_use_def:
  mssa_get_memory_use ms inst_id = FLOOKUP ms.ms_inst_use inst_id
End

(* ==========================================================================
   Query: Clobber walk

   Walks up the reaching-def chain from an access to find the most
   recent definition that completely_contains the query location.
   For MemPhi: recurse into each operand.
     - 0 clobbering operands → NONE (no clobber on any path)
     - 1 clobbering operand  → SOME that operand
     - ≥2 clobbering operands → SOME the phi itself (conservative)
   ========================================================================== *)

(* Collect clobbers from phi operands given a walker function. *)
Definition mssa_collect_phi_clobbers_def:
  mssa_collect_phi_clobbers walker [] = [] ∧
  mssa_collect_phi_clobbers walker ((rd, _)::ops) =
    case walker rd of
      NONE => mssa_collect_phi_clobbers walker ops
    | SOME c => c :: mssa_collect_phi_clobbers walker ops
End

Definition mssa_walk_clobber_def:
  mssa_walk_clobber ms 0 visited current qloc = NONE ∧
  mssa_walk_clobber ms (SUC fuel) visited current qloc =
    if current = 0 then NONE
    else if MEM current visited then NONE
    else
      let visited' = current :: visited in
      case FLOOKUP ms.ms_nodes current of
        NONE => NONE
      | SOME (MnDef _ _ def_loc) =>
          if completely_contains def_loc qloc then SOME current
          else
            (case FLOOKUP ms.ms_reaching current of
               NONE => NONE
             | SOME rd => mssa_walk_clobber ms fuel visited' rd qloc)
      | SOME (MnUse _ _ _) =>
          (case FLOOKUP ms.ms_reaching current of
             NONE => NONE
           | SOME rd => mssa_walk_clobber ms fuel visited' rd qloc)
      | SOME (MnPhi _) =>
          (case FLOOKUP ms.ms_phi_ops current of
             NONE => NONE
           | SOME ops =>
               let clobbers = mssa_collect_phi_clobbers
                 (λrd. mssa_walk_clobber ms fuel visited' rd qloc) ops in
               case clobbers of
                 [] => NONE
               | [c] => SOME c
               | _ => SOME current)
End

(* Top-level clobber query.
 * Returns NONE if given LiveOnEntry (id 0).
 * Returns SOME 0 (LiveOnEntry) if no store clobbers the location.
 * Returns SOME access_id of the clobbering definition otherwise. *)
Definition mssa_get_clobbered_def:
  mssa_get_clobbered ms fuel access_id =
    if access_id = 0 then NONE
    else
      case FLOOKUP ms.ms_nodes access_id of
        NONE => NONE
      | SOME node =>
          let qloc = mn_loc node in
          case FLOOKUP ms.ms_reaching access_id of
            NONE => SOME 0
          | SOME rd =>
              (case mssa_walk_clobber ms fuel [] rd qloc of
                 NONE => SOME 0
               | SOME c => SOME c)
End

(* ==========================================================================
   Query: Aliased accesses walk

   Walk up the reaching-def chain and collect all MemDef nodes whose
   locations may_alias with the query location.
   ========================================================================== *)

(* Collect aliased accesses from phi operands given a walker function. *)
Definition mssa_collect_phi_aliased_def:
  mssa_collect_phi_aliased walker [] = [] ∧
  mssa_collect_phi_aliased walker ((rd, _)::ops) =
    walker rd ++ mssa_collect_phi_aliased walker ops
End

Definition mssa_walk_aliased_def:
  mssa_walk_aliased ms alias 0 visited current qloc = [] ∧
  mssa_walk_aliased ms alias (SUC fuel) visited current qloc =
    if current = 0 then []
    else if MEM current visited then []
    else
      let visited' = current :: visited in
      let from_here =
        case FLOOKUP ms.ms_nodes current of
          NONE => []
        | SOME (MnDef _ _ def_loc) =>
            if ma_may_alias alias qloc def_loc then [current] else []
        | SOME (MnUse _ _ _) => []
        | SOME (MnPhi _) =>
            (case FLOOKUP ms.ms_phi_ops current of
               NONE => []
             | SOME ops =>
                 mssa_collect_phi_aliased
                   (λrd. mssa_walk_aliased ms alias fuel visited' rd qloc)
                   ops)
      in
      let from_chain =
        case FLOOKUP ms.ms_reaching current of
          NONE => []
        | SOME rd => mssa_walk_aliased ms alias fuel visited' rd qloc
      in
      from_here ++ from_chain
End

Definition mssa_get_aliased_def:
  mssa_get_aliased ms alias fuel access_id =
    if access_id = 0 then []
    else
      let qloc = case FLOOKUP ms.ms_nodes access_id of
                   SOME node => mn_loc node
                 | NONE => ml_empty in
      mssa_walk_aliased ms alias fuel [] access_id qloc
End

(* ==========================================================================
   Mark location volatile
   ========================================================================== *)

Definition mssa_mark_volatile_def:
  mssa_mark_volatile ms alias loc =
    let (vloc, alias') = ma_mark_volatile alias loc in
    (* Update any def whose location aliases with loc to be volatile *)
    let ms' = ms with
      ms_nodes :=
        FOLDL (λnodes (aid, node).
          case node of
            MnDef iid blk dloc =>
              if ma_may_alias alias dloc loc
              then nodes |+ (aid, MnDef iid blk (mk_volatile dloc))
              else nodes
          | _ => nodes)
        ms.ms_nodes (fmap_to_alist ms.ms_nodes)
    in
    (vloc, ms', alias')
End

(* ==========================================================================
   Three address-space instantiations
   ========================================================================== *)

Definition memory_ssa_analyze_def:
  memory_ssa_analyze cfg dom bp fn =
    mssa_build cfg dom bp fn AddrSp_Memory
End

Definition storage_ssa_analyze_def:
  storage_ssa_analyze cfg dom bp fn =
    mssa_build cfg dom bp fn AddrSp_Storage
End

Definition transient_ssa_analyze_def:
  transient_ssa_analyze cfg dom bp fn =
    mssa_build cfg dom bp fn AddrSp_Transient
End

