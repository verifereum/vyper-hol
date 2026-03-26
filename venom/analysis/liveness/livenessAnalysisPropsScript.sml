(*
 * Liveness Analysis Properties (Statements Only)
 *
 * FROZEN — do not modify statements. Proofs via ACCEPT_TAC from livenessProofs.
 *
 * 1) Boundedness — live variables come from the function's instructions.
 * 2) Soundness — if v is live, it is used before redefinition on some path.
 * 3) Transfer equations — intra-block and cross-block liveness propagation.
 * 4) Forward propagation — not-live and live-or-used forward reasoning.
 *)

Theory livenessAnalysisProps
Ancestors
  livenessProofs

(* ==========================================================================
   1) Boundedness
   ========================================================================== *)

Theorem live_vars_bounded:
  ∀fn lbl idx v.
    let st = liveness_analyze fn in
    MEM v (live_vars_at st lbl idx) ⇒
    MEM v (fn_all_vars fn.fn_blocks)
Proof
  ACCEPT_TAC live_vars_bounded_proof
QED

(* ==========================================================================
   2) Soundness
   ========================================================================== *)

Theorem liveness_sound:
  ∀fn lbl idx v.
    let cfg = cfg_analyze fn in
    let st = liveness_analyze fn in
    let bbs = fn.fn_blocks in
    wf_function fn ∧
    MEM v (live_vars_at st lbl idx) ⇒
    ∃path.
      cfg_exec_path cfg ((lbl, idx) :: path) ∧
      used_before_defined bbs v ((lbl, idx) :: path)
Proof
  ACCEPT_TAC liveness_sound_proof
QED

(* ==========================================================================
   3) Intra-block transfer equations
   ========================================================================== *)

(* live_vars_at at idx = transfer(inst[idx], live_vars_at at idx+1) *)
Theorem live_vars_at_transfer:
  ∀fn lbl bb idx.
    wf_function fn ⇒
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre ∧
    lookup_block lbl fn.fn_blocks = SOME bb ∧
    SUC idx ≤ LENGTH bb.bb_instructions ⇒
    live_vars_at lr lbl idx =
      liveness_transfer fn.fn_blocks (EL idx bb.bb_instructions)
        (live_vars_at lr lbl (SUC idx))
Proof
  ACCEPT_TAC livenessProofsTheory.live_vars_at_transfer
QED

(* A variable used at instruction idx is live at idx *)
Theorem live_vars_at_uses:
  ∀fn lbl bb idx v.
    wf_function fn ⇒
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre ∧
    lookup_block lbl fn.fn_blocks = SOME bb ∧
    idx < LENGTH bb.bb_instructions ∧
    MEM v (inst_uses (EL idx bb.bb_instructions)) ⇒
    MEM v (live_vars_at lr lbl idx)
Proof
  ACCEPT_TAC livenessProofsTheory.live_vars_at_uses
QED

(* If live at idx+1 and not killed at idx, then live at idx *)
Theorem live_vars_at_propagate:
  ∀fn lbl bb idx v.
    wf_function fn ⇒
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre ∧
    lookup_block lbl fn.fn_blocks = SOME bb ∧
    idx < LENGTH bb.bb_instructions ∧
    MEM v (live_vars_at lr lbl (SUC idx)) ∧
    ¬MEM v (inst_defs (EL idx bb.bb_instructions)) ⇒
    MEM v (live_vars_at lr lbl idx)
Proof
  ACCEPT_TAC livenessProofsTheory.live_vars_at_propagate
QED

(* Propagate liveness backward from j to i when not killed in [i,j) *)
Theorem live_vars_at_propagate_range:
  ∀fn lbl bb i j v.
    wf_function fn ⇒
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre ∧
    lookup_block lbl fn.fn_blocks = SOME bb ∧
    i ≤ j ∧ j ≤ LENGTH bb.bb_instructions ∧
    MEM v (live_vars_at lr lbl j) ∧
    (∀k. i ≤ k ∧ k < j ⇒ ¬MEM v (inst_defs (EL k bb.bb_instructions))) ⇒
    MEM v (live_vars_at lr lbl i)
Proof
  ACCEPT_TAC livenessProofsTheory.live_vars_at_propagate_range
QED

(* ==========================================================================
   4) Cross-block liveness transfer
   ========================================================================== *)

(* If v is live at entry of successor and v is not a PHI output there,
   then v is live at exit of predecessor *)
Theorem live_vars_at_cross_block:
  ∀fn pred_lbl pred_bb succ_lbl succ_bb v.
    wf_function fn ⇒
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM pred_lbl cfg.cfg_dfs_pre ∧
    MEM succ_lbl cfg.cfg_dfs_pre ∧
    MEM succ_lbl (cfg_succs_of cfg pred_lbl) ∧
    lookup_block pred_lbl fn.fn_blocks = SOME pred_bb ∧
    lookup_block succ_lbl fn.fn_blocks = SOME succ_bb ∧
    MEM v (live_vars_at lr succ_lbl 0) ∧
    (∀inst. MEM inst (collect_phis succ_bb.bb_instructions) ⇒
            ¬MEM v inst.inst_outputs) ⇒
    MEM v (live_vars_at lr pred_lbl (LENGTH pred_bb.bb_instructions))
Proof
  ACCEPT_TAC livenessProofsTheory.live_vars_at_cross_block
QED

(* ==========================================================================
   5) Forward propagation (contrapositives)
   ========================================================================== *)

(* If v is not live at i and not defined in [i,j), then not live at j *)
Theorem not_live_forward_in_block:
  ∀fn lbl bb i j v.
    wf_function fn ⇒
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre ∧
    lookup_block lbl fn.fn_blocks = SOME bb ∧
    i ≤ j ∧ j ≤ LENGTH bb.bb_instructions ∧
    ¬MEM v (live_vars_at lr lbl i) ∧
    (∀k. i ≤ k ∧ k < j ⇒ ¬MEM v (inst_defs (EL k bb.bb_instructions))) ⇒
    ¬MEM v (live_vars_at lr lbl j)
Proof
  ACCEPT_TAC livenessProofsTheory.not_live_forward_in_block
QED

(* If v is not live at exit of predecessor and no PHI output for v in
   successor, then v is not live at entry of successor *)
Theorem not_live_cross_block:
  ∀fn pred_lbl pred_bb succ_lbl succ_bb v.
    wf_function fn ⇒
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM pred_lbl cfg.cfg_dfs_pre ∧
    MEM succ_lbl cfg.cfg_dfs_pre ∧
    MEM succ_lbl (cfg_succs_of cfg pred_lbl) ∧
    lookup_block pred_lbl fn.fn_blocks = SOME pred_bb ∧
    lookup_block succ_lbl fn.fn_blocks = SOME succ_bb ∧
    ¬MEM v (live_vars_at lr pred_lbl (LENGTH pred_bb.bb_instructions)) ∧
    (∀inst. MEM inst (collect_phis succ_bb.bb_instructions) ⇒
            ¬MEM v inst.inst_outputs) ⇒
    ¬MEM v (live_vars_at lr succ_lbl 0)
Proof
  ACCEPT_TAC livenessProofsTheory.not_live_cross_block
QED

(* If v is live at i and not killed in [i,j), then either v is live at j
   or v is used at some position in [i,j) *)
Theorem live_vars_at_forward_or_used:
  ∀fn lbl bb i j v.
    wf_function fn ⇒
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre ∧
    lookup_block lbl fn.fn_blocks = SOME bb ∧
    i ≤ j ∧ j ≤ LENGTH bb.bb_instructions ∧
    MEM v (live_vars_at lr lbl i) ∧
    (∀k. i ≤ k ∧ k < j ⇒ ¬MEM v (inst_defs (EL k bb.bb_instructions))) ⇒
    MEM v (live_vars_at lr lbl j) ∨
    (∃k. i ≤ k ∧ k < j ∧ MEM v (inst_uses (EL k bb.bb_instructions)))
Proof
  ACCEPT_TAC livenessProofsTheory.live_vars_at_forward_or_used
QED
