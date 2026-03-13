(*
 * Remove Unused Variables — Definitions
 *
 * Ports vyper/venom/passes/remove_unused_variables.py to HOL4.
 *
 * Removes instructions that produce outputs never used, provided
 * the instruction is not volatile and not a terminator.
 *
 * Approach: liveness-based iterated removal.
 *   1. Run liveness analysis on current function
 *   2. NOP any removable instruction whose outputs are all dead
 *      (except: memory-expanding instructions protected by msize_fence)
 *   3. Clear NOPs, repeat until fixpoint (OWHILE)
 *
 * The iteration is needed because standard liveness counts uses from
 * dead instructions — removing one dead instruction can make another's
 * output dead. Each iteration removes ≥1 instruction, so OWHILE
 * terminates (bounded by total instruction count).
 *
 * The msize_fence prevents removing memory-expanding instructions
 * when a live MSIZE downstream would observe the memory size change.
 * This matches Python's special MSIZE cascade handling.
 *
 * TOP-LEVEL:
 *   remove_unused_inst     — per-instruction transform (given live set)
 *   msize_fence            — fence using only surviving MSIZEs
 *   remove_unused_function — function-level transform (iterated)
 *)

Theory removeUnusedDefs
Libs
  pred_setLib
Ancestors
  analysisSimDefs livenessDefs passSharedDefs venomEffects cfgDefs While

(* ===== Per-instruction transform ===== *)

(* Transform given the set of live variables after this instruction
   and whether an MSIZE instruction is reachable from here.
   If the instruction is removable and none of its outputs are live,
   replace with NOP — UNLESS the instruction has memory write effects
   and an MSIZE is reachable (msize_fence).

   Python logic: if MSIZE ∈ write_effects(inst) and msize_fence(inst)
   then don't remove, because the memory write affects MSIZE result. *)
Definition remove_unused_inst_def:
  remove_unused_inst (live : string list) (has_msize_fence : bool) inst =
    if ~is_removable inst then inst
    else if has_msize_fence /\
            Eff_MSIZE IN write_effects inst.inst_opcode
    then inst  (* msize fence: don't remove memory-expanding instructions *)
    else if EVERY (\v. ~MEM v live) inst.inst_outputs
    then mk_nop_inst inst
    else inst
End

(* ===== Liveness query ===== *)

(* Query live-after for instruction at index idx.
   live_vars_at returns live_before, so:
   - for non-last instructions: live_after[idx] = live_before[idx+1]
   - for last instruction: live_after = block out_vars *)
Definition live_after_at_def:
  live_after_at (lr : liveness_result) lbl idx n_insts =
    if idx + 1 < n_insts then live_vars_at lr lbl (idx + 1)
    else out_vars_of lr lbl
End

(* ===== MSIZE fence computation ===== *)

(* A surviving MSIZE is one whose output is live (won't be removed
   by the same pass). Pre-computing this is equivalent to Python's
   worklist cascade where removing dead MSIZE unblocks memory-writers. *)

(* Does this block contain a surviving (live-output) MSIZE? *)
Definition block_has_live_msize_def:
  block_has_live_msize (lr : liveness_result) bb =
    let n = LENGTH bb.bb_instructions in
    EXISTS (\(idx, inst).
      inst.inst_opcode = MSIZE /\
      EXISTS (\v. MEM v (live_after_at lr bb.bb_label idx n))
        inst.inst_outputs)
      (MAPi (\i inst. (i, inst)) bb.bb_instructions)
End

(* Block labels that contain a surviving MSIZE *)
Definition live_msize_blocks_def:
  live_msize_blocks lr fn =
    MAP (\bb. bb.bb_label)
      (FILTER (block_has_live_msize lr) fn.fn_blocks)
End

(* Is there a surviving MSIZE in any block reachable (via 1+ CFG
   edges) from bb_lbl? Uses cfg_path (RTC of successors) from cfgDefs.
   Starts from bb_lbl's successors so bb_lbl is only included
   if reachable from itself via a cycle — matching Python's
   ReachableAnalysis which is fused into cfg_analyze. *)
Definition msize_reachable_from_def:
  msize_reachable_from lr cfg fn bb_lbl =
    EXISTS (\lbl.
      (?succ. MEM succ (cfg_succs_of cfg bb_lbl) /\
              cfg_path cfg succ lbl))
      (live_msize_blocks lr fn)
End

(* Is there a surviving MSIZE after instruction at index idx in
   this block? Only counts MSIZEs whose output is live. *)
Definition has_live_msize_after_def:
  has_live_msize_after (lr : liveness_result) bb_label n_insts
                       bb_insts idx =
    EXISTS (\(j, inst).
      inst.inst_opcode = MSIZE /\
      EXISTS (\v. MEM v (live_after_at lr bb_label j n_insts))
        inst.inst_outputs)
      (MAPi (\i inst. (idx + 1 + i, inst)) (DROP (idx + 1) bb_insts))
End

(* msize_fence using only surviving MSIZEs.
   True if a surviving MSIZE could execute after the current instruction:
   1. Any reachable block has a surviving MSIZE
   2. A surviving MSIZE later in the same block *)
Definition msize_fence_def:
  msize_fence lr cfg fn bb_lbl idx bb_insts <=>
    msize_reachable_from lr cfg fn bb_lbl \/
    has_live_msize_after lr bb_lbl (LENGTH bb_insts) bb_insts idx
End

(* ===== Function-level transform ===== *)

Definition remove_unused_block_def:
  remove_unused_block (lr : liveness_result) (fence : num -> bool) bb =
    let n = LENGTH bb.bb_instructions in
    bb with bb_instructions :=
      MAPi (\idx inst.
        remove_unused_inst (live_after_at lr bb.bb_label idx n)
                           (fence idx) inst)
        bb.bb_instructions
End

(* Single pass: transform + clear NOPs *)
Definition remove_unused_single_pass_def:
  remove_unused_single_pass fn =
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    clear_nops_function
      (function_map_transform
        (\bb. remove_unused_block lr
                (\idx. msize_fence lr cfg fn bb.bb_label idx
                                  bb.bb_instructions)
                bb)
        fn)
End

(* Iterate until fixpoint: matches Python's worklist behavior.
   Each iteration recomputes liveness (since removing instructions
   changes liveness results). OWHILE terminates because each changed
   iteration removes at least one instruction, strictly decreasing
   the total instruction count. *)
Definition remove_unused_iterate_def:
  remove_unused_iterate fn =
    OWHILE (\fn. remove_unused_single_pass fn <> fn)
           remove_unused_single_pass fn
End

Definition remove_unused_function_def:
  remove_unused_function fn =
    case remove_unused_iterate fn of
      SOME fn' => fn'
    | NONE => fn
End

(* Variables eliminated by remove_unused: outputs of NOP'd instructions.
   These are dead (no live use) — their values don't affect any
   observable behavior. The correctness theorem excludes them from
   state equivalence. *)
Definition remove_unused_eliminated_vars_def:
  remove_unused_eliminated_vars fn =
    let fn' = remove_unused_function fn in
    (* Outputs present in original but absent in transformed *)
    set (FLAT (MAP (\bb.
      FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
      fn.fn_blocks)) DIFF
    set (FLAT (MAP (\bb.
      FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
      fn'.fn_blocks))
End
