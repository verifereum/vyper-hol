(* Block-level invariant obligations for algebraic optimization.
 *
 * Obligations for block_sim_function_error_bb in
 * ao_phases123_run_blocks_sim_inv (algebraicOptProofsScript.sml):
 *
 *   1-4. block_inv preserved through exec_block
 *   5-6. Initial state establishment
 *
 * block_inv s = ao_dfg_inv dfg (s with vs_inst_idx := 0) /\
 *               ao_iszero_chain_inv targets s /\
 *               ao_chains_defined targets s /\
 *               range_sound (df_widen_at NONE ra s.vs_current_bb 0) s /\
 *               MEM s.vs_current_bb (cfg_analyze fn0).cfg_dfs_pre
 *
 * The ao_dfg_inv preservation is already proved inline via
 * ao_dfg_inv_exec_block_preserved. These obligations handle the
 * remaining components.
 *
 * Proof strategy:
 *   chain_inv/chains_defined through exec_block:
 *     Induct on exec_block (following ao_dfg_inv_exec_block_preserved).
 *     At each step, use ao_iszero_chain_inv_step_preserved /
 *     ao_chains_defined_step_preserved with SSA side condition.
 *   range_sound + cfg at successor:
 *     Use range_successor_obligation from assertElimProofs, which
 *     provides both range_sound and cfg membership at the successor.
 *     Requires dfg_sound — either track it in block_inv or prove a
 *     specialized version.
 *   Initial state:
 *     chain_inv: vacuously true (chain vars undefined → antecedent false).
 *     chains_defined: requires chain vars to be defined at initial state.
 *       May need precondition strengthening or invariant reformulation.
 *     range_sound: trivially true at entry block (FEMPTY range state).
 *     cfg: entry block in DFS preorder from wf_function.
 *)

Theory aoBlockInvObligation
Ancestors
  algebraicOptDefs aoResolveObligation aoRangeObligation
  stateEquiv venomWf venomExecSemantics venomExecProofs
  analysisSimDefs rangeAnalysisProofs
  passSharedDefs cfgDefs cfgHelpers
  venomInst venomInstProps
Libs
  pairLib BasicProvers

(* ===== Block-level preservation ===== *)

(* ao_iszero_chain_inv preserved through exec_block.
   Follow the pattern of ao_dfg_inv_exec_block_preserved:
   induct on exec_block, apply step_preserved at each step
   with SSA side condition. *)
Theorem ao_chain_inv_exec_block_preserved:
  !fn0 dfg targets bb fuel ctx s v.
    dfg = dfg_build_function fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    ssa_form fn0 /\
    wf_function fn0 /\
    EVERY inst_wf bb.bb_instructions /\
    MEM bb fn0.fn_blocks /\
    ao_iszero_chain_inv targets s /\
    exec_block fuel ctx bb s = OK v ==>
    ao_iszero_chain_inv targets v
Proof
  cheat
QED

(* ao_chains_defined preserved through exec_block. *)
Theorem ao_chains_defined_exec_block_preserved:
  !fn0 dfg targets bb fuel ctx s v.
    dfg = dfg_build_function fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    ssa_form fn0 /\
    wf_function fn0 /\
    EVERY inst_wf bb.bb_instructions /\
    MEM bb fn0.fn_blocks /\
    ao_chains_defined targets s /\
    exec_block fuel ctx bb s = OK v ==>
    ao_chains_defined targets v
Proof
  cheat
QED

(* range_sound + cfg membership at successor block after exec_block.
   Uses range_successor_obligation from assertElimProofs.
   May need dfg_sound as additional precondition. *)
Theorem ao_block_inv_successor:
  !fn0 dfg ra bb fuel ctx s v.
    dfg = dfg_build_function fn0 /\
    ra = range_analyze fn0 /\
    wf_function fn0 /\
    ssa_form fn0 /\
    EVERY inst_wf (fn_insts fn0) /\
    MEM bb fn0.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn0).cfg_dfs_pre /\
    s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
    range_sound (df_widen_at NONE ra bb.bb_label 0) s /\
    ao_dfg_inv dfg (s with vs_inst_idx := 0) /\
    exec_block fuel ctx bb s = OK v ==>
    range_sound (df_widen_at NONE ra v.vs_current_bb 0) v /\
    MEM v.vs_current_bb (cfg_analyze fn0).cfg_dfs_pre
Proof
  cheat
QED

(* ===== Initial state ===== *)

(* ao_iszero_chain_inv at initial state: vacuously true when
   chain operand variables are undefined (eval_operand = NONE). *)
Theorem ao_chain_inv_initial:
  !fn fn0 targets s.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    ssa_form fn /\ wf_function fn /\
    (!x inst. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
      lookup_var x s = NONE) ==>
    ao_iszero_chain_inv targets s
Proof
  cheat
QED

(* ao_chains_defined at initial state.
   NOTE: This obligation may require strengthening the top-level
   theorem's preconditions, or reformulating the invariant to be
   conditional on variable definedness. The current formulation
   requires ALL chain operands to have defined values, which may
   not hold at the initial state if chain operands are Var references
   to instruction outputs that haven't been computed yet.
   Possible fix: weaken ao_chains_defined to only require definedness
   for chain elements that are Lit/Label (always defined), or make
   chains_defined conditional and adjust the per-instruction sim. *)
Theorem ao_chains_defined_initial:
  !fn fn0 targets s.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    ssa_form fn /\ wf_function fn /\
    (!x inst. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
      lookup_var x s = NONE) ==>
    ao_chains_defined targets s
Proof
  cheat
QED

(* range_sound at initial state: trivially true for entry block.
   At function entry, df_widen_at NONE ra entry_lbl 0 is the
   initial range state (NONE or SOME FEMPTY), and range_sound
   for those is trivially true. *)
Theorem ao_range_sound_initial:
  !fn0 ra s.
    ra = range_analyze fn0 /\
    wf_function fn0 ==>
    range_sound (df_widen_at NONE ra s.vs_current_bb 0) s
Proof
  cheat
QED

(* Entry block is in cfg_dfs_pre for well-formed functions. *)
Theorem ao_cfg_initial:
  !fn0 s.
    wf_function fn0 /\
    fn_entry_label fn0 = SOME s.vs_current_bb ==>
    MEM s.vs_current_bb (cfg_analyze fn0).cfg_dfs_pre
Proof
  rpt strip_tac >>
  fs[fn_entry_label_def, entry_block_def, cfg_analyze_def] >>
  gvs[wf_function_def, fn_has_entry_def] >>
  Cases_on `fn0.fn_blocks` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  `SND (dfs_pre_walk (build_succs (h::t)) [] h.bb_label) <> [] /\
   HD (SND (dfs_pre_walk (build_succs (h::t)) [] h.bb_label)) = h.bb_label` by
    (irule dfs_pre_walk_entry_hd >> simp[]) >>
  Cases_on `SND (dfs_pre_walk (build_succs (h::t)) [] h.bb_label)` >> gvs[]
QED
