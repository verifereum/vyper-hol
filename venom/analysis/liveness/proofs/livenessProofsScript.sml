(* Public liveness API: transport the recomputation proofs. *)
Theory livenessProofs
Ancestors
  livenessLocalProofs livenessSoundProofs
Libs
  livenessDefsTheory livenessTransferProofsTheory
  livenessLocalProofsTheory livenessSoundProofsTheory
  livenessConvergenceProofsTheory cfgAnalysisPropsTheory

Theorem live_vars_bounded_proof:
  !fn lbl idx v.
    let st = liveness_analyze fn in
    MEM v (live_vars_at st lbl idx) ==> MEM v (fn_all_vars fn.fn_blocks)
Proof
  rewrite_tac[liveness_analyze_def] >> ACCEPT_TAC liveness_recompute_bounded
QED

Theorem liveness_sound_proof:
  !fn lbl idx v.
    let cfg = cfg_analyze fn in
    let st = liveness_analyze fn in
    let bbs = fn.fn_blocks in
    wf_function fn /\ MEM v (live_vars_at st lbl idx) ==>
    ?path. cfg_exec_path cfg ((lbl,idx)::path) /\
           used_before_defined bbs v ((lbl,idx)::path)
Proof
  rewrite_tac[liveness_analyze_def] >> ACCEPT_TAC liveness_recompute_sound
QED

(* The exit is a set fixpoint of the current successor gather. *)
Theorem liveness_convergence:
  wf_function fn /\ cfg_reachable_of (cfg_analyze fn) lbl ==>
  same_vars
    (df_at [] (liveness_analyze fn) lbl
      (LENGTH (liveness_instrs fn.fn_blocks lbl)))
    (liveness_out fn.fn_blocks (cfg_analyze fn) lbl (liveness_analyze fn))
Proof
  simp[liveness_analyze_def, liveness_recompute_convergence]
QED

Theorem live_at_entry_in_boundary:
  wf_function fn /\ cfg_reachable_of (cfg_analyze fn) lbl ==>
  df_boundary [] (liveness_analyze fn) lbl =
  live_vars_at (liveness_analyze fn) lbl 0
Proof
  simp[liveness_analyze_def, liveness_recompute_boundary_entry]
QED

Theorem live_vars_at_transfer:
  !fn lbl bb idx.
    wf_function fn ==>
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre /\ lookup_block lbl fn.fn_blocks = SOME bb /\
    SUC idx <= LENGTH bb.bb_instructions ==>
    live_vars_at lr lbl idx =
      liveness_transfer fn.fn_blocks (EL idx bb.bb_instructions)
        (live_vars_at lr lbl (SUC idx))
Proof
  rewrite_tac[liveness_analyze_def] >> ACCEPT_TAC liveness_recompute_transfer
QED

Theorem live_vars_at_uses:
  !fn lbl bb idx v.
    wf_function fn ==>
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre /\ lookup_block lbl fn.fn_blocks = SOME bb /\
    idx < LENGTH bb.bb_instructions /\
    MEM v (inst_uses (EL idx bb.bb_instructions)) ==>
    MEM v (live_vars_at lr lbl idx)
Proof
  rewrite_tac[liveness_analyze_def] >> ACCEPT_TAC liveness_recompute_uses
QED

Theorem live_vars_at_propagate:
  !fn lbl bb idx v.
    wf_function fn ==>
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre /\ lookup_block lbl fn.fn_blocks = SOME bb /\
    idx < LENGTH bb.bb_instructions /\
    MEM v (live_vars_at lr lbl (SUC idx)) /\
    ~MEM v (inst_defs (EL idx bb.bb_instructions)) ==>
    MEM v (live_vars_at lr lbl idx)
Proof
  rewrite_tac[liveness_analyze_def] >> ACCEPT_TAC liveness_recompute_propagate
QED

Theorem live_vars_at_propagate_range:
  !fn lbl bb i j v.
    wf_function fn ==>
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre /\ lookup_block lbl fn.fn_blocks = SOME bb /\
    i <= j /\ j <= LENGTH bb.bb_instructions /\
    MEM v (live_vars_at lr lbl j) /\
    (!k. i <= k /\ k < j ==> ~MEM v (inst_defs (EL k bb.bb_instructions))) ==>
    MEM v (live_vars_at lr lbl i)
Proof
  rewrite_tac[liveness_analyze_def] >> ACCEPT_TAC liveness_recompute_propagate_range
QED

Theorem input_vars_from_non_phi:
  !lbl instrs live v.
    MEM v live /\
    (!inst. MEM inst (collect_phis instrs) ==>
       ~MEM v (MAP SND (phi_pairs inst.inst_operands))) ==>
    MEM v (input_vars_from lbl instrs live)
Proof
  ACCEPT_TAC recompute_input_vars_from_non_phi
QED

Theorem live_vars_at_cross_block:
  !fn pred_lbl pred_bb succ_lbl succ_bb v.
    wf_function fn ==>
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM pred_lbl cfg.cfg_dfs_pre /\ MEM succ_lbl cfg.cfg_dfs_pre /\
    MEM succ_lbl (cfg_succs_of cfg pred_lbl) /\
    lookup_block pred_lbl fn.fn_blocks = SOME pred_bb /\
    lookup_block succ_lbl fn.fn_blocks = SOME succ_bb /\
    MEM v (live_vars_at lr succ_lbl 0) /\
    (!inst. MEM inst (collect_phis succ_bb.bb_instructions) ==>
       ~MEM v (MAP SND (phi_pairs inst.inst_operands))) ==>
    MEM v (live_vars_at lr pred_lbl (LENGTH pred_bb.bb_instructions))
Proof
  rewrite_tac[liveness_analyze_def] >> ACCEPT_TAC liveness_recompute_cross_block
QED

Theorem not_live_forward_in_block:
  !fn lbl bb i j v.
    wf_function fn ==>
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre /\ lookup_block lbl fn.fn_blocks = SOME bb /\
    i <= j /\ j <= LENGTH bb.bb_instructions /\
    ~MEM v (live_vars_at lr lbl i) /\
    (!k. i <= k /\ k < j ==> ~MEM v (inst_defs (EL k bb.bb_instructions))) ==>
    ~MEM v (live_vars_at lr lbl j)
Proof
  rewrite_tac[liveness_analyze_def] >> ACCEPT_TAC liveness_recompute_not_live_forward
QED

Theorem not_live_cross_block:
  !fn pred_lbl pred_bb succ_lbl succ_bb v.
    wf_function fn ==>
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM pred_lbl cfg.cfg_dfs_pre /\ MEM succ_lbl cfg.cfg_dfs_pre /\
    MEM succ_lbl (cfg_succs_of cfg pred_lbl) /\
    lookup_block pred_lbl fn.fn_blocks = SOME pred_bb /\
    lookup_block succ_lbl fn.fn_blocks = SOME succ_bb /\
    ~MEM v (live_vars_at lr pred_lbl (LENGTH pred_bb.bb_instructions)) /\
    (!inst. MEM inst (collect_phis succ_bb.bb_instructions) ==>
       ~MEM v (MAP SND (phi_pairs inst.inst_operands))) ==>
    ~MEM v (live_vars_at lr succ_lbl 0)
Proof
  rewrite_tac[liveness_analyze_def] >> ACCEPT_TAC liveness_recompute_not_live_cross_block
QED

Theorem live_vars_at_forward_or_used:
  !fn lbl bb i j v.
    wf_function fn ==>
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre /\ lookup_block lbl fn.fn_blocks = SOME bb /\
    i <= j /\ j <= LENGTH bb.bb_instructions /\
    MEM v (live_vars_at lr lbl i) /\
    (!k. i <= k /\ k < j ==> ~MEM v (inst_defs (EL k bb.bb_instructions))) ==>
    MEM v (live_vars_at lr lbl j) \/
    (?k. i <= k /\ k < j /\ MEM v (inst_uses (EL k bb.bb_instructions)))
Proof
  rewrite_tac[liveness_analyze_def] >> ACCEPT_TAC liveness_recompute_forward_or_used
QED

(* Retain independently used transfer interfaces for existing consumers. *)
Theorem collect_phis_mem:
  !instrs inst. MEM inst (collect_phis instrs) ==>
    MEM inst instrs /\ inst.inst_opcode = PHI
Proof
  ACCEPT_TAC livenessTransferProofsTheory.collect_phis_mem
QED

Theorem live_update_mem:
  MEM v (live_update defs uses live) <=>
    (MEM v live /\ ~MEM v defs) \/ MEM v uses
Proof
  ACCEPT_TAC livenessTransferProofsTheory.live_update_mem
QED

val _ = List.app (fn (_,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
  then () else raise Fail "oracle in public liveness API")
  (DB.thms "livenessProofs");
