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
  algebraicOptDefs algebraicOptWf aoResolveObligation aoRangeObligation
  stateEquiv venomWf venomExecSemantics venomExecProofs
  analysisSimDefs rangeAnalysisProofs
  passSharedDefs cfgDefs cfgHelpers
  venomInst venomInstProps venomState
Libs
  pairLib BasicProvers

(* ===== Block-level preservation ===== *)

(* ao_iszero_chain_inv preserved through exec_block.
   BLOCKER: ao_iszero_chain_inv_step_preserved requires chain operand
   evaluations unchanged, which fails when the current instruction IS
   an iszero defining a chain variable. Need a stronger step lemma
   that handles the iszero case: when step_inst computes iszero(chain[k]),
   the newly-defined chain[k+1] satisfies the invariant. This lemma
   belongs in aoResolveObligation alongside the existing step_preserved.
   Alternatively, split into two cases:
     - Non-chain instructions: use ao_iszero_chain_inv_step_preserved
       with SSA side condition (step_preserves_non_output_vars)
     - Chain (iszero) instructions: prove directly from step_inst semantics
   Also needs step_terminator_preserves_vars for terminators. *)
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

(* ao_chains_defined preserved through exec_block.
   BLOCKER: Similar to chain_inv - needs ao_chains_defined_step_preserved
   with SSA side condition. For non-iszero instructions, chain operand
   evaluations are unchanged (SSA). For iszero instructions, the newly
   computed output variable becomes defined, which strengthens chains_defined.
   Needs step_preserves_non_output_vars + step_terminator_preserves_vars. *)
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
(* ===== Helper: chain element at position >= 1 is an output ===== *)

(* Single step: new chain from ao_compute_iszero_step has output vars
   at all positions >= 1. *)
Triviality chain_el_step_output[local]:
  !acc inst v chain k.
    ALOOKUP (ao_compute_iszero_step acc inst) v = SOME chain /\
    0 < k /\ k < LENGTH chain ==>
    (?x. EL k chain = Var x /\ MEM x inst.inst_outputs) \/
    (?v' chain' k'. ALOOKUP acc v' = SOME chain' /\
       0 < k' /\ k' < LENGTH chain' /\ EL k' chain' = EL k chain)
Proof
  rpt gen_tac >>
  simp[ao_compute_iszero_step_def, LET_THM] >>
  every_case_tac >> simp[] >>
  strip_tac >> gvs[listTheory.LENGTH_SNOC] >>
  TRY (DISJ2_TAC >> qexistsl_tac [`v`, `chain`, `k`] >> simp[] >> NO_TAC) >>
  TRY (qexistsl_tac [`v`, `chain`, `k`] >> simp[] >> NO_TAC) >>
  Cases_on `h = v` >> gvs[] >>
  TRY (DISJ2_TAC >> qexistsl_tac [`v`, `chain`, `k`] >> simp[] >> NO_TAC) >>
  Cases_on `k` >>
  gvs[listTheory.EL_restricted, listTheory.HD,
      listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC] >>
  TRY (Cases_on `n` >>
       gvs[listTheory.HD, listTheory.EL_restricted] >> NO_TAC) >>
  rename1 `SUC m` >>
  Cases_on `SUC m = LENGTH x` >>
  gvs[listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC] >>
  DISJ2_TAC >>
  qexistsl_tac [`s`, `x`, `SUC m`] >> gvs[]
QED

(* Inductive: all chain elements at position >= 1 come from
   instruction outputs in the FOLDL. *)
Triviality chain_el_foldl_output[local]:
  !insts acc v chain k.
    ALOOKUP (FOLDL ao_compute_iszero_step acc insts) v = SOME chain /\
    0 < k /\ k < LENGTH chain ==>
    (?x inst. EL k chain = Var x /\ MEM inst insts /\
              MEM x inst.inst_outputs) \/
    (?v' ch' k'. ALOOKUP acc v' = SOME ch' /\
       0 < k' /\ k' < LENGTH ch' /\ EL k' ch' = EL k chain)
Proof
  Induct >> rpt strip_tac
  >- (gvs[] >> qexistsl_tac [`v`, `chain`, `k`] >> simp[])
  >- (first_x_assum
        (qspecl_then [`ao_compute_iszero_step acc h`,
                      `v`, `chain`, `k`] mp_tac) >>
      impl_tac >- gvs[Once listTheory.FOLDL] >>
      strip_tac
      >- (DISJ1_TAC >> metis_tac[listTheory.MEM])
      >- (metis_tac[chain_el_step_output, listTheory.MEM]))
QED

(* fn0 instruction outputs = fn instruction outputs modulo
   ao_handle_offset_inst (which preserves outputs). *)
Triviality fn0_output_is_fn_output_helper[local]:
  !blocks inst x.
    MEM inst (fn_insts_blocks
      (MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) blocks)) /\
    MEM x inst.inst_outputs ==>
    ?inst'. MEM inst' (fn_insts_blocks blocks) /\ MEM x inst'.inst_outputs
Proof
  Induct >> simp[fn_insts_blocks_def] >>
  rpt strip_tac >>
  gvs[fn_insts_blocks_def, listTheory.MEM_APPEND, listTheory.MEM_MAP]
  >- (qexists_tac `y` >>
      gvs[ao_handle_offset_inst_outputs, listTheory.MEM_APPEND])
  >- (first_x_assum drule_all >> strip_tac >>
      qexists_tac `inst'` >> simp[listTheory.MEM_APPEND])
QED

Triviality fn0_output_is_fn_output[local]:
  !fn fn0 inst x.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    MEM inst (fn_insts fn0) /\ MEM x inst.inst_outputs ==>
    ?inst'. MEM inst' (fn_insts fn) /\ MEM x inst'.inst_outputs
Proof
  rpt strip_tac >> gvs[fn_insts_def] >>
  irule fn0_output_is_fn_output_helper >> metis_tac[]
QED

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
  rpt strip_tac >> gvs[] >>
  simp[ao_iszero_chain_inv_def] >> rpt strip_tac >>
  `0 < k + 1 /\ k + 1 < LENGTH chain` by simp[] >>
  qpat_x_assum `ALOOKUP _ v = SOME chain` mp_tac >>
  simp[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
  strip_tac >>
  drule_all chain_el_foldl_output >> strip_tac
  >> fs[fn_insts_def] >>
  drule fn0_output_is_fn_output_helper >>
  disch_then drule >>
  strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `eval_operand (Var _) _ = _` mp_tac >>
  REWRITE_TAC[eval_operand_def] >> gvs[]
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

(* range_sound at initial state.
   BLOCKER: Theorem is quantified over ALL s (any state, any bb label).
   For blocks NOT in cfg_dfs_pre, FLOOKUP ra.dws_inst (lbl,0) = NONE
   and range_sound NONE s = T (by range_sound_bottom). For blocks in
   cfg_dfs_pre, df_widen_at returns the analysis result which may be
   non-trivial. Needs df_analyze_widen_all_P from dfAnalyzeWidenProps
   instantiated with P = (λv. ∀s. range_sound v s), showing closure
   under range_join_opt, range_widen_opt, range_transfer_opt, and
   range_edge_transfer_opt. Base cases: range_sound_bottom (NONE)
   and range_sound_fempty (entry_val). May need to reformulate the
   theorem to only state range_sound at the entry block, or add
   a constraint on s.vs_current_bb. *)
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
