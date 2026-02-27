(*
 * Liveness Analysis — Definitions
 *
 * Ports vyper/venom/analysis/liveness.py to HOL4.
 *
 * TOP-LEVEL:
 *   liveness_analyze      — run full liveness analysis on a function
 *   liveness_result       — record: out_vars, inst_liveness per block
 *   live_vars_at          — query liveness at an instruction index
 *   out_vars_of           — query live-out vars of a block
 *   input_vars_from       — live vars entering target from source (PHI-aware)
 *
 * From venomInst:
 *   inst_uses / inst_defs — input/output variables of an instruction
 *   phi_pairs             — extract (label, var) pairs from PHI operands
 *
 * Helper:
 *   live_update           — (live - defs) ∪ uses
 *   calculate_liveness    — backward transfer for one block
 *   calculate_out_vars    — compute out_vars from successors
 *   liveness_one_pass     — process all blocks once (in postorder)
 *   liveness_iterate      — iterate passes until fixpoint
 *   total_live_count      — measure for termination
 *   all_var_slots         — upper bound on total_live_count
 *)

Theory livenessDefs
Ancestors
  list finite_map pred_set
  venomInst cfgDefs dfIterateDefs

(* inst_uses, inst_defs, phi_pairs come from venomInst *)

(* ==========================================================================
   Set-as-list helpers (no duplicates invariant)
   ========================================================================== *)

(* Remove elements of rm from xs, then append elements of add not in result.
   Models: (live \ defs) ∪ uses *)
Definition live_update_def:
  live_update defs uses live =
    let live' = FILTER (λv. ¬MEM v defs) live in
    live' ++ FILTER (λv. ¬MEM v live') uses
End

(* Merge: xs ∪ ys as list (no dups if xs has no dups). *)
Definition list_union_def:
  list_union xs ys = xs ++ FILTER (λv. ¬MEM v xs) ys
End

(* ==========================================================================
   PHI-aware input_vars_from

   Given edge source→target, compute which variables are live.
   For each PHI in target: include operand for source, exclude others.
   ========================================================================== *)

(* phi_pairs comes from venomInst *)

Definition input_vars_from_def:
  input_vars_from src_label target_instrs base_liveness =
    FOLDL
      (λlive inst.
        if inst.inst_opcode ≠ PHI then live
        else
          let pairs = phi_pairs inst.inst_operands in
          let add_vars = MAP SND (FILTER (λ(l,v). l = src_label) pairs) in
          let rm_vars  = MAP SND (FILTER (λ(l,v). l ≠ src_label) pairs) in
          let live' = FILTER (λv. ¬MEM v rm_vars) live in
          list_union live' add_vars)
      base_liveness
      target_instrs
End

(* ==========================================================================
   Result types
   ========================================================================== *)

Datatype:
  block_liveness = <|
    bl_out_vars : string list;
    bl_inst_liveness : (num, string list) fmap
  |>
End

Datatype:
  liveness_result = <|
    lr_blocks : (string, block_liveness) fmap
  |>
End

(* ==========================================================================
   Query API
   ========================================================================== *)

Definition empty_block_liveness_def:
  empty_block_liveness = <|
    bl_out_vars := [];
    bl_inst_liveness := FEMPTY
  |>
End

Definition lookup_block_liveness_def:
  lookup_block_liveness lr lbl =
    case FLOOKUP lr.lr_blocks lbl of
      NONE => empty_block_liveness
    | SOME bl => bl
End

Definition out_vars_of_def:
  out_vars_of lr lbl = (lookup_block_liveness lr lbl).bl_out_vars
End

Definition live_vars_at_def:
  live_vars_at lr lbl idx =
    let bl = lookup_block_liveness lr lbl in
    case FLOOKUP bl.bl_inst_liveness idx of
      NONE => []
    | SOME vars => vars
End

(* Count leading PHI instructions. *)
Definition count_phis_def:
  count_phis [] = (0:num) ∧
  count_phis (inst::rest) =
    if inst.inst_opcode ≠ PHI then 0
    else 1 + count_phis rest
End

(* Live-in variables = liveness at the first non-PHI instruction. *)
Definition liveness_in_vars_def:
  liveness_in_vars lr bb =
    let i = count_phis bb.bb_instructions in
    if i < LENGTH bb.bb_instructions then
      live_vars_at lr bb.bb_label i
    else []
End

(* ==========================================================================
   Backward transfer: calculate_liveness

   Walk instructions in reverse, threading liveness backward.
   Returns updated block_liveness.
   ========================================================================== *)

Definition calc_liveness_loop_def:
  calc_liveness_loop instrs live 0 =
    (let inst = EL 0 instrs in
     let uses = inst_uses inst in
     let defs = inst_defs inst in
     let live' = if NULL uses ∧ NULL defs then live
                 else live_update defs uses live in
     (live', FEMPTY |+ (0, live'))) ∧
  calc_liveness_loop instrs live (SUC n) =
    let inst = EL (SUC n) instrs in
    let uses = inst_uses inst in
    let defs = inst_defs inst in
    let live' = if NULL uses ∧ NULL defs then live
                else live_update defs uses live in
    let (final_live, m) = calc_liveness_loop instrs live' n in
    (final_live, m |+ (SUC n, live'))
End

Definition calculate_liveness_def:
  calculate_liveness bb (bl : block_liveness) =
    let instrs = bb.bb_instructions in
    if NULL instrs then bl
    else
      let n = LENGTH instrs - 1 in
      let (_, inst_map) = calc_liveness_loop instrs bl.bl_out_vars n in
      bl with bl_inst_liveness := inst_map
End

(* ==========================================================================
   calculate_out_vars

   out_vars(bb) = ∪ { input_vars_from(bb, succ) | succ ∈ cfg_succs(bb) }
   ========================================================================== *)

Definition calculate_out_vars_def:
  calculate_out_vars cfg lr bb bbs =
    let succ_labels = cfg_succs_of cfg bb.bb_label in
    FOLDL
      (λacc succ_lbl.
        case lookup_block succ_lbl bbs of
          NONE => acc
        | SOME succ_bb =>
            let base = live_vars_at lr succ_lbl 0 in
            let target_vars =
              input_vars_from bb.bb_label succ_bb.bb_instructions base in
            list_union acc target_vars)
      [] succ_labels
End

(* ==========================================================================
   Process one block: update out_vars then backward-transfer liveness.
   ========================================================================== *)

(* Merge new out_vars with existing (ensures monotonicity for all inputs,
   not just those reachable from init — needed for termination). *)
Definition process_block_def:
  process_block cfg bbs lr bb =
    let new_out = calculate_out_vars cfg lr bb bbs in
    let bl = lookup_block_liveness lr bb.bb_label in
    let merged_out = list_union bl.bl_out_vars new_out in
    let bl' = bl with bl_out_vars := merged_out in
    let bl'' = calculate_liveness bb bl' in
    lr with lr_blocks := lr.lr_blocks |+ (bb.bb_label, bl'')
End

(* ==========================================================================
   One full pass: process all blocks in the given order.
   ========================================================================== *)

Definition liveness_one_pass_def:
  liveness_one_pass cfg bbs lr [] = lr ∧
  liveness_one_pass cfg bbs lr (lbl::rest) =
    let lr' =
      case lookup_block lbl bbs of
        NONE => lr
      | SOME bb => process_block cfg bbs lr bb in
    liveness_one_pass cfg bbs lr' rest
End

(* ==========================================================================
   Measure for termination

   total_live_count = sum of lengths of all live sets across all blocks.
   all_var_slots = upper bound (total instruction slots × variable count).
   When the result changes, total_live_count strictly increases.
   ========================================================================== *)

(* All variable names mentioned anywhere in a function. *)
Definition fn_all_vars_def:
  fn_all_vars bbs =
    FLAT (MAP (λbb.
      FLAT (MAP (λinst. inst_uses inst ++ inst_defs inst)
                bb.bb_instructions))
      bbs)
End

(* Total number of instruction slots across all blocks. *)
Definition fn_total_insts_def:
  fn_total_insts bbs = SUM (MAP (λbb. LENGTH bb.bb_instructions) bbs)
End

(* Count of live variables across all inst_liveness maps + all out_vars.
   Used as termination measure (increases monotonically). *)
Definition block_live_count_def:
  block_live_count bl =
    LENGTH bl.bl_out_vars +
    SUM (MAP (λ(k,vs). LENGTH vs) (fmap_to_alist bl.bl_inst_liveness))
End

Definition total_live_count_def:
  total_live_count lr =
    SUM (MAP (λ(k,bl). block_live_count bl)
      (fmap_to_alist lr.lr_blocks))
End

(* Upper bound: each slot can hold at most |all_vars| variables. *)
Definition all_var_slots_def:
  all_var_slots bbs =
    let nv = LENGTH (nub (fn_all_vars bbs)) in
    let ni = fn_total_insts bbs + LENGTH bbs in  (* +|bbs| for out_vars *)
    nv * ni
End

(* ==========================================================================
   Iterate passes until fixpoint via df_iterate (WHILE-based).

   The step function is liveness_one_pass with fixed cfg/bbs/order.
   Convergence follows from:
     - inflationary: total_live_count strictly increases on non-fixpoint steps
       (guaranteed by list_union merge in process_block)
     - bounded: total_live_count ≤ all_var_slots
   ========================================================================== *)

Definition liveness_iterate_def:
  liveness_iterate cfg bbs order lr =
    df_iterate (λlr'. liveness_one_pass cfg bbs lr' order) lr
End

(* ==========================================================================
   Top-level: initialize and iterate
   ========================================================================== *)

Definition init_liveness_def:
  init_liveness bbs =
    <| lr_blocks :=
         FOLDL (λm bb. m |+ (bb.bb_label, empty_block_liveness))
               FEMPTY bbs |>
End

Definition liveness_analyze_def:
  liveness_analyze fn =
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let lr0 = init_liveness bbs in
    let order = cfg.cfg_dfs_post in
    liveness_iterate cfg bbs order lr0
End

(* ==========================================================================
   Ordering on liveness results (for monotonicity statements)
   ========================================================================== *)

(* Pointwise ordering: lr1 ≤ lr2 when every live set in lr1 is a subset
   of the corresponding set in lr2. *)
Definition lr_leq_def:
  lr_leq lr1 lr2 =
    ((∀lbl. set (out_vars_of lr1 lbl) ⊆ set (out_vars_of lr2 lbl)) ∧
     (∀lbl idx. set (live_vars_at lr1 lbl idx) ⊆ set (live_vars_at lr2 lbl idx)))
End

(* ==========================================================================
   Execution path and use/def at a point (for soundness statement)
   ========================================================================== *)

(* An execution path through the CFG: a list of (block_label, inst_index)
   positions visited in order.  Consecutive positions are either
   within the same block (idx+1) or across a CFG edge (new block, idx 0). *)
Definition cfg_exec_path_def:
  cfg_exec_path cfg ([] : (string # num) list) = T ∧
  cfg_exec_path cfg [(lbl, idx)] = T ∧
  cfg_exec_path cfg ((lbl1, idx1) :: (lbl2, idx2) :: rest) =
    (((lbl1 = lbl2 ∧ idx2 = idx1 + 1) ∨
      (lbl1 ≠ lbl2 ∧ MEM lbl2 (cfg_succs_of cfg lbl1) ∧ idx2 = 0)) ∧
     cfg_exec_path cfg ((lbl2, idx2) :: rest))
End

(* Variable v is used (read) at position (lbl, idx). *)
Definition var_used_at_def:
  var_used_at bbs lbl idx v =
    (∃bb inst.
      lookup_block lbl bbs = SOME bb ∧
      idx < LENGTH bb.bb_instructions ∧
      EL idx bb.bb_instructions = inst ∧
      MEM v (inst_uses inst))
End

(* Variable v is defined (written) at position (lbl, idx). *)
Definition var_defined_at_def:
  var_defined_at bbs lbl idx v =
    (∃bb inst.
      lookup_block lbl bbs = SOME bb ∧
      idx < LENGTH bb.bb_instructions ∧
      EL idx bb.bb_instructions = inst ∧
      MEM v (inst_defs inst))
End

(* v is used-before-defined along a position sequence: there exists some
   position k where v is used, and v is not defined at any earlier position. *)
Definition used_before_defined_def:
  used_before_defined bbs v positions =
    (∃k. k < LENGTH positions ∧
         var_used_at bbs (FST (EL k positions)) (SND (EL k positions)) v ∧
         ∀j. j < k ==>
             ¬var_defined_at bbs (FST (EL j positions))
                                 (SND (EL j positions)) v)
End
