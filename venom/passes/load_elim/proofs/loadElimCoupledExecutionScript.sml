Theory loadElimCoupledExecution
Ancestors
  loadElimCaptureEntry loadElimCaptureSteps loadElimCaptureInvariant loadElimPrependIndex
  loadElimOccurrenceInvariants loadElimReachedLoad loadElimReachedStore
  loadElimPaddedCalls loadElimPaddedNoncall loadElimMemoryRel
  loadElimActionSelection loadElimLatestJoin loadElimOccurrence loadElimDefs
  loadElimSentinelHelpers loadElimKeyShapeInvariant cfgAnalysisProps
  instIdxIndep analysisSimProofsBase venomInstProps contextCodegenRel opcodeClass
  venomState venomInst venomExecSemantics venomExecProps venomExecProofs stateFrame stateEquiv list

(* Entry/edge coupling is le_padded_control.  Inside a block only the
   instruction index differs; captures refer to completed source events. *)
Definition le_body_coupling_def:
  le_body_coupling m ctx cfg result actions h bb s t <=>
    padded_exec_equiv {v | isPREFIX "$le_phi_" v} s t /\
    s.vs_current_bb = t.vs_current_bb /\
    s.vs_prev_bb = t.vs_prev_bb /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH (phis_for_block actions bb.bb_label) /\
    phi_prefix_length bb.bb_instructions <= s.vs_inst_idx /\
    le_latest_captures m ctx cfg result actions h t
End

Theorem le_body_coupling_normalize:
  le_body_coupling m ctx cfg result actions h bb s t ==>
  le_padded_control {v | isPREFIX "$le_phi_" v}
    (s with vs_inst_idx := 0) (t with vs_inst_idx := 0)
Proof
  simp[le_body_coupling_def, le_padded_control_def,
       padded_exec_equiv_def, lookup_var_def, read_memory_def,
       execution_frame_def]
QED

Theorem le_latest_captures_idx[simp]:
  le_latest_captures m ctx cfg result actions h (t with vs_inst_idx := n) =
  le_latest_captures m ctx cfg result actions h t
Proof
  simp[le_latest_captures_def, lookup_var_def]
QED

Theorem le_body_coupling_enter:
  le_padded_control {v | isPREFIX "$le_phi_" v} p q /\
  le_latest_captures m ctx cfg result actions h q ==>
  le_body_coupling m ctx cfg result actions h bb
    (p with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    (q with vs_inst_idx := phi_prefix_length bb.bb_instructions +
       LENGTH (phis_for_block actions bb.bb_label))
Proof
  simp[le_body_coupling_def, le_padded_control_def,
       padded_exec_equiv_def, lookup_var_def, read_memory_def,
       execution_frame_def]
QED

Theorem le_body_coupling_increment:
  le_body_coupling m ctx cfg result actions h bb s t /\
  padded_exec_equiv {v | isPREFIX "$le_phi_" v} u v /\
  u.vs_current_bb = v.vs_current_bb /\ u.vs_prev_bb = v.vs_prev_bb /\
  le_latest_captures m ctx cfg result actions h' v ==>
  le_body_coupling m ctx cfg result actions h' bb
    (u with vs_inst_idx := SUC s.vs_inst_idx)
    (v with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  simp[le_body_coupling_def, padded_exec_equiv_def,
       lookup_var_def, read_memory_def, execution_frame_def] >>
  decide_tac
QED

(* Static and initial obligations shared by the continuation induction.
   In particular this does not assert a target run or a local simulation. *)
Definition le_round_ready_def:
  le_round_ready C fn ctx s0 <=>
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
    le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
    (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
    ctx.lctx_aliases = ma_analyze ctx.lctx_bp fn ctx.lctx_addr_space /\
    fn_entry_label fn = SOME s0.vs_current_bb /\
    is_fixpoint (df_process_block Forward NONE load_join load_transfer
      load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
      (load_analyze ctx fn) /\
    dfg_assigns_sound (dfg_build_function fn) s0 /\
    bp_ptr_sound ctx.lctx_bp s0 /\ alloca_inv s0 /\ allocas_in_word s0 /\
    bp_ptrs_bounded ctx.lctx_bp fn s0 /\
    le_step_preserves ctx.lctx_bp (dfg_build_function fn) fn /\
    (!bb u t. MEM bb fn.fn_blocks /\
      MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
      eval_phis u bb.bb_instructions = OK t /\
      dfg_assigns_sound (dfg_build_function fn) u ==>
      dfg_assigns_sound (dfg_build_function fn) t) /\
    EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) /\
    EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts fn) /\
    EVERY (\f. EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts f)) C.ctx_functions
End

Theorem le_body_coupling_fetch:
  le_configured_context ctx /\
  le_body_coupling m ctx cfg result actions h bb s t /\
  get_instruction bb s.vs_inst_idx = SOME i ==>
  get_instruction
    (analysis_block_transform_prepend NONE result (load_phi_prepend actions)
      (\ll inst. [load_elim_inst ctx actions ll inst]) bb) t.vs_inst_idx =
    SOME (load_elim_inst ctx actions (df_at NONE result bb.bb_label s.vs_inst_idx) i)
Proof
  simp[le_body_coupling_def, Excl "isPREFIX"] >> rpt strip_tac >>
  metis_tac[le_actual_prepend_get_instruction, arithmeticTheory.ADD_COMM]
QED

Theorem le_coupled_captured_load:
  le_round_ready C fn ctx s0 /\
  le_occ_prefix C fn s0 h i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  le_body_coupling m ctx (cfg_analyze fn) (load_analyze ctx fn)
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) h bb s t /\
  inst_wf i /\ step_inst k C i s = OK s' /\
  phi_action_lookup
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
    i.inst_id = SOME out ==>
  ?t'. step_inst k C
    (load_elim_inst ctx
      (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
      (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx) i) t = OK t' /\
    padded_exec_equiv {v | isPREFIX "$le_phi_" v} s' t' /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_prev_bb = s.vs_prev_bb /\ s'.vs_inst_idx = s.vs_inst_idx /\
    t'.vs_current_bb = t.vs_current_bb /\
    t'.vs_prev_bb = t.vs_prev_bb /\ t'.vs_inst_idx = t.vs_inst_idx
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   EL s.vs_inst_idx bb.bb_instructions = i` by fs[get_instruction_def] >>
  rule_assum_tac (PURE_REWRITE_RULE [le_round_ready_def, le_body_coupling_def]) >>
  RULE_L_ASSUM_TAC CONJUNCTS >>
  drule_all le_collected_action_at_position >> strip_tac >>
  `pa.pa_load_lbl = s.vs_current_bb` by metis_tac[] >>
  drule_all le_reached_collected_action_latest_join >> strip_tac >>
  `?w. le_key_read ctx.lctx_addr_space
     (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
       (normalize_operand ctx.lctx_dfg []) i) u = SOME w /\
     lookup_var pa.pa_phi_out t = SOME w` by
    (fs[le_latest_captures_def, Excl "isPREFIX"] >> metis_tac[]) >>
  qpat_x_assum `h = _` SUBST_ALL_TAC >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  qpat_assum `bb.bb_label = s.vs_current_bb`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  qpat_assum `pa.pa_phi_out = out`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [GSYM th])) >>
  irule le_reached_captured_load_replacement >>
  simp[Excl "isPREFIX"] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  goal_assum (drule_at Any) >>
  simp[Excl "isPREFIX"] >>
  qpat_assum `ctx.lctx_dfg = _`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  qpat_assum `s.vs_current_bb = t.vs_current_bb`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  rpt (goal_assum (drule_at Any) >> simp[Excl "isPREFIX"])
QED

Theorem le_source_operand_lookup_agreement:
  MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) /\
  padded_exec_equiv {v | isPREFIX "$le_phi_" v} s t ==>
  !v. MEM (Var v) i.inst_operands ==> lookup_var v s = lookup_var v t
Proof
  rpt strip_tac >>
  `MEM v (fn_all_vars fn)` by
    metis_tac[cfgNormBaseTheory.inst_operand_var_in_fn_all_vars] >>
  `~isPREFIX "$le_phi_" v` by
    (qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_MEM, Excl "isPREFIX"]) >>
  fs[padded_exec_equiv_def, Excl "isPREFIX"]
QED

(* Full instruction boundary at equal control indices, including INVOKE. *)
Theorem le_padded_source_step:
  le_padded_control V s t /\
  (!v. MEM (Var v) i.inst_operands ==> lookup_var v s = lookup_var v t) /\
  i.inst_opcode <> MEMTOP /\
  EVERY (\f. EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts f)) C.ctx_functions ==>
  (?e. step_inst fuel C i s = Error e) \/
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst fuel C i s) (step_inst fuel C i t)
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (`!name ops. decode_invoke i = SOME (name,ops) ==>
        eval_operands ops s = eval_operands ops t` by
        (rpt strip_tac >> irule le_padded_operands_agreement >>
         (reverse conj_tac >-
           (qexists_tac `V` >> fs[le_padded_control_def])) >>
         rpt strip_tac >> first_x_assum irule >>
         gvs[decode_invoke_def, AllCaseEqs()] >> simp[]) >>
      irule le_padded_invoke_step >> simp[]) >>
  disj2_tac >> simp[step_inst_def] >>
  irule le_padded_noncall_step >> simp[]
QED

Theorem le_coupled_unchanged_nonterm:
  le_padded_control V (s with vs_inst_idx := 0) (t with vs_inst_idx := 0) /\
  (!v. MEM (Var v) i.inst_operands ==> lookup_var v s = lookup_var v t) /\
  i.inst_opcode <> MEMTOP /\ ~is_terminator i.inst_opcode /\
  EVERY (\f. EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts f)) C.ctx_functions /\
  step_inst fuel C i s = OK u ==>
  ?v. step_inst fuel C i t = OK v /\ padded_exec_equiv V u v /\
      u.vs_current_bb = v.vs_current_bb /\ u.vs_prev_bb = v.vs_prev_bb /\
      u.vs_inst_idx = s.vs_inst_idx /\ v.vs_inst_idx = t.vs_inst_idx
Proof
  strip_tac >>
  drule_all le_step_nonterm_rebase_OK >>
  disch_then (qspec_then `0` strip_assume_tac) >>
  `!v. MEM (Var v) i.inst_operands ==>
    lookup_var v (s with vs_inst_idx := 0) =
    lookup_var v (t with vs_inst_idx := 0)` by fs[lookup_var_def] >>
  drule_all le_padded_source_step >>
  disch_then (qspec_then `fuel` mp_tac) >> simp[lift_result_def] >>
  Cases_on `step_inst fuel C i (t with vs_inst_idx := 0)` >>
  simp[lift_result_def] >> strip_tac >>
  drule_all le_step_nonterm_from_zero >> strip_tac >>
  goal_assum (drule_at Any) >>
  fs[le_padded_control_def, padded_exec_equiv_def, lookup_var_def,
     read_memory_def, execution_frame_def]
QED

Theorem le_coupled_unchanged_term:
  le_padded_control V (s with vs_inst_idx := 0) (t with vs_inst_idx := 0) /\
  (!v. MEM (Var v) i.inst_operands ==> lookup_var v s = lookup_var v t) /\
  i.inst_opcode <> MEMTOP /\ is_terminator i.inst_opcode /\
  EVERY (\f. EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts f)) C.ctx_functions /\
  step_inst fuel C i s = OK u ==>
  ?v. step_inst fuel C i t = OK v /\ le_padded_control V u v
Proof
  strip_tac >>
  drule_all le_step_term_rebase_OK >>
  disch_then (qspec_then `0` strip_assume_tac) >>
  `!v. MEM (Var v) i.inst_operands ==>
    lookup_var v (s with vs_inst_idx := 0) =
    lookup_var v (t with vs_inst_idx := 0)` by fs[lookup_var_def] >>
  drule_all le_padded_source_step >>
  disch_then (qspec_then `fuel` mp_tac) >> simp[lift_result_def] >>
  Cases_on `step_inst fuel C i (t with vs_inst_idx := 0)` >>
  simp[lift_result_def] >> strip_tac >>
  drule_all le_step_term_from_zero >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem le_coupled_changed_step:
  le_round_ready C fn ctx s0 /\
  le_occ_prefix C fn s0 h i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  le_body_coupling m ctx (cfg_analyze fn) (load_analyze ctx fn)
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) h bb s t /\
  inst_wf i /\ step_inst k C i s = OK s' /\
  load_elim_inst ctx
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx) i <> i ==>
  ?t'. step_inst k C
    (load_elim_inst ctx
      (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
      (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx) i) t = OK t' /\
    padded_exec_equiv {v | isPREFIX "$le_phi_" v} s' t' /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_prev_bb = s.vs_prev_bb /\ s'.vs_inst_idx = s.vs_inst_idx /\
    t'.vs_current_bb = t.vs_current_bb /\
    t'.vs_prev_bb = t.vs_prev_bb /\ t'.vs_inst_idx = t.vs_inst_idx
Proof
  strip_tac >>
  drule (SRULE [] (Q.INST
    [`transformed` |-> `load_elim_inst ctx actions ll inst`]
    loadElimOriginHelpersTheory.load_elim_inst_changed)) >>
  strip_tac
  >- (rule_assum_tac (PURE_REWRITE_RULE [le_round_ready_def, le_body_coupling_def]) >>
      RULE_L_ASSUM_TAC CONJUNCTS >>
      irule le_reached_singleton_load_replacement >>
      simp[Excl "isPREFIX"] >>
      rpt (goal_assum (drule_at Any) >> simp[Excl "isPREFIX"]))
  >- (irule le_coupled_captured_load >>
      rpt (goal_assum (drule_at Any) >> simp[Excl "isPREFIX"])) >>
  rule_assum_tac (PURE_REWRITE_RULE [le_round_ready_def, le_body_coupling_def]) >>
  RULE_L_ASSUM_TAC CONJUNCTS >>
  irule le_reached_store_replacement >>
  simp[Excl "isPREFIX"] >>
  rpt (goal_assum (drule_at Any) >> simp[Excl "isPREFIX"])
QED

Theorem le_coupled_source_nonterm:
  le_round_ready C fn ctx s0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  le_body_coupling m ctx cfg result actions h bb s t /\
  ~is_terminator i.inst_opcode /\ step_inst k C i s = OK u ==>
  ?v. step_inst k C i t = OK v /\
    padded_exec_equiv {v | isPREFIX "$le_phi_" v} u v /\
    u.vs_current_bb = v.vs_current_bb /\ u.vs_prev_bb = v.vs_prev_bb /\
    u.vs_inst_idx = s.vs_inst_idx /\ v.vs_inst_idx = t.vs_inst_idx
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM i bb.bb_instructions` by
    (fs[get_instruction_def] >> metis_tac[MEM_EL]) >>
  `le_padded_control {v | isPREFIX "$le_phi_" v}
     (s with vs_inst_idx := 0) (t with vs_inst_idx := 0)` by
    metis_tac[le_body_coupling_normalize] >>
  rule_assum_tac (PURE_REWRITE_RULE [le_round_ready_def, le_body_coupling_def]) >>
  RULE_L_ASSUM_TAC CONJUNCTS >>
  `!v. MEM (Var v) i.inst_operands ==> lookup_var v s = lookup_var v t` by
    (rpt strip_tac >> irule le_source_operand_lookup_agreement >> metis_tac[]) >>
  `i.inst_opcode <> MEMTOP` by
    (qpat_x_assum `EVERY _ (fn_insts fn)` mp_tac >>
     simp[EVERY_MEM] >> disch_then irule >>
     simp[fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[]) >>
  irule le_coupled_unchanged_nonterm >> simp[]
QED

Theorem le_coupled_nonterm_step:
  le_round_ready C fn ctx s0 /\
  le_occ_prefix C fn s0 h i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  le_body_coupling m ctx (cfg_analyze fn) (load_analyze ctx fn)
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) h bb s t /\
  inst_wf i /\ ~is_terminator i.inst_opcode /\ step_inst k C i s = OK u ==>
  ?v. step_inst k C
    (load_elim_inst ctx
      (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
      (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx) i) t = OK v /\
    le_body_coupling m ctx (cfg_analyze fn) (load_analyze ctx fn)
      (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
      (h ++ [StepOcc bb s.vs_inst_idx k s u]) bb
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >>
  `?v. step_inst k C
    (load_elim_inst ctx
      (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
      (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx) i) t = OK v /\
    padded_exec_equiv {v | isPREFIX "$le_phi_" v} u v /\
    u.vs_current_bb = v.vs_current_bb /\ u.vs_prev_bb = v.vs_prev_bb` by
    (Cases_on `load_elim_inst ctx
      (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
      (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx) i = i`
     >- (drule_all le_coupled_source_nonterm >> metis_tac[]) >>
     drule_all le_coupled_changed_step >> strip_tac >>
     fs[le_body_coupling_def, Excl "isPREFIX"] >> metis_tac[]) >>
  goal_assum (drule_at Any) >>
  irule le_body_coupling_increment >>
  goal_assum (drule_at Any) >> simp[] >>
  (reverse conj_tac >- (qexists_tac `h` >> first_assum ACCEPT_TAC)) >>
  irule le_latest_captures_transformed_step >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM i bb.bb_instructions` by
    (fs[get_instruction_def] >> metis_tac[MEM_EL]) >>
  rule_assum_tac (PURE_REWRITE_RULE [le_round_ready_def, le_body_coupling_def]) >>
  RULE_L_ASSUM_TAC CONJUNCTS >>
  rpt (goal_assum (drule_at Any) >> simp[Excl "isPREFIX"])
QED

Theorem le_configured_terminator_unchanged:
  le_configured_context ctx /\ is_terminator i.inst_opcode ==>
  load_elim_inst ctx actions ll i = i
Proof
  strip_tac >> irule loadElimOriginHelpersTheory.load_elim_inst_unchanged >>
  gvs[le_configured_context_def, memory_config_def, storage_config_def,
      transient_config_def, dload_config_def, calldataload_config_def] >>
  Cases_on `i.inst_opcode` >> fs[is_terminator_def]
QED

Theorem le_step_result_normalize_idx:
  exec_result_map (\u. u with vs_inst_idx := 0)
    (step_inst fuel C i (s with vs_inst_idx := n)) =
  exec_result_map (\u. u with vs_inst_idx := 0) (step_inst fuel C i s)
Proof
  Cases_on `i.inst_opcode = INVOKE`
  >- (simp[invoke_step_inst_idx_OK_only] >>
      Cases_on `step_inst fuel C i s` >> simp[exec_result_map_def]) >>
  Cases_on `is_terminator i.inst_opcode`
  >- (simp[step_inst_def, terminator_step_inst_base_idx_norm0]) >>
  simp[step_inst_idx_indep] >>
  Cases_on `step_inst fuel C i s` >> simp[exec_result_map_def]
QED

Theorem le_padded_lift_normalize_idx:
  lift_result
    (\s t. le_padded_control V (s with vs_inst_idx := 0) (t with vs_inst_idx := 0))
    (padded_exec_equiv V) (padded_exec_equiv V)
    (exec_result_map (\s. s with vs_inst_idx := 0) r)
    (exec_result_map (\s. s with vs_inst_idx := 0) q) =
  lift_result
    (\s t. le_padded_control V (s with vs_inst_idx := 0) (t with vs_inst_idx := 0))
    (padded_exec_equiv V) (padded_exec_equiv V) r q
Proof
  Cases_on `r` >> Cases_on `q` >>
  simp[lift_result_def, exec_result_map_def, padded_exec_equiv_def,
       lookup_var_def, read_memory_def, execution_frame_def]
QED

Theorem le_step_error_normalize_idx:
  (step_inst fuel C i (s with vs_inst_idx := n) = Error e) =
  (step_inst fuel C i s = Error e)
Proof
  mp_tac le_step_result_normalize_idx >>
  Cases_on `step_inst fuel C i (s with vs_inst_idx := n)` >>
  Cases_on `step_inst fuel C i s` >> simp[exec_result_map_def]
QED

Theorem le_padded_source_step_normalized:
  le_padded_control V (s with vs_inst_idx := 0) (t with vs_inst_idx := 0) /\
  (!v. MEM (Var v) i.inst_operands ==> lookup_var v s = lookup_var v t) /\
  i.inst_opcode <> MEMTOP /\
  EVERY (\f. EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts f)) C.ctx_functions ==>
  (?e. step_inst fuel C i s = Error e) \/
  lift_result
    (\u v. le_padded_control V (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst fuel C i s) (step_inst fuel C i t)
Proof
  strip_tac >>
  `!v. MEM (Var v) i.inst_operands ==>
    lookup_var v (s with vs_inst_idx := 0) =
    lookup_var v (t with vs_inst_idx := 0)` by fs[lookup_var_def] >>
  `lift_result
    (\u v. le_padded_control V (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst fuel C i (s with vs_inst_idx := 0))
    (step_inst fuel C i (t with vs_inst_idx := 0)) =
   lift_result
    (\u v. le_padded_control V (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst fuel C i s) (step_inst fuel C i t)` by
    (once_rewrite_tac[GSYM le_padded_lift_normalize_idx] >>
     pure_rewrite_tac[le_step_result_normalize_idx] >>
     simp[le_padded_lift_normalize_idx]) >>
  drule_all le_padded_source_step >>
  disch_then (qspec_then `fuel` mp_tac) >>
  simp[le_step_error_normalize_idx] >> strip_tac >- simp[] >>
  disj2_tac >> first_x_assum (SUBST1_TAC o GSYM) >>
  Cases_on `step_inst fuel C i (s with vs_inst_idx := 0)` >>
  Cases_on `step_inst fuel C i (t with vs_inst_idx := 0)` >>
  fs[lift_result_def] >> metis_tac[le_padded_control_idx]
QED

Theorem le_transformed_nonterm:
  ~is_terminator i.inst_opcode ==>
  ~is_terminator (load_elim_inst ctx actions ll i).inst_opcode
Proof
  strip_tac >> Cases_on `load_elim_inst ctx actions ll i = i` >- simp[] >>
  drule_at (Pat `transformed <> inst`) loadElimOriginHelpersTheory.load_elim_inst_changed >>
  disch_then (qspecl_then [`ll`, `ctx`, `actions`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[passSharedDefsTheory.mk_assign_inst_def, passSharedDefsTheory.mk_nop_inst_def,
      is_terminator_def]
QED

(* Successful block exits retain the final source instruction occurrence.
   This is the evidence needed to enter successor PHIs, not merely a
   relation on the two exit states. *)
Theorem le_coupled_block_OK:
  !n s h t i u.
  n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
  le_round_ready C fn ctx s0 /\
  le_occ_prefix C fn s0 h i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  le_body_coupling m ctx (cfg_analyze fn) (load_analyze ctx fn)
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) h bb s t /\
  exec_block k C bb s = OK u ==>
  ?v h' j x.
    exec_block k C
      (analysis_block_transform_prepend NONE (load_analyze ctx fn)
        (load_phi_prepend (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn))
        (\ll inst. [load_elim_inst ctx
          (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) ll inst]) bb) t = OK v /\
    le_padded_control {v | isPREFIX "$le_phi_" v} u v /\
    le_occ_prefix C fn s0 h' j x /\
    lookup_block x.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb x.vs_inst_idx = SOME j /\
    is_terminator j.inst_opcode /\ step_inst k C j x = OK u /\ ~u.vs_halted /\
    le_latest_captures m ctx (cfg_analyze fn) (load_analyze ctx fn)
      (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
      (h' ++ [StepOcc bb x.vs_inst_idx k x u]) v
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM i bb.bb_instructions` by
    (fs[get_instruction_def] >> metis_tac[MEM_EL]) >>
  `inst_wf i` by
    (fs[le_round_ready_def] >> metis_tac[fn_inst_wf_every_bb, EVERY_MEM]) >>
  qpat_x_assum `exec_block k C bb s = OK u` mp_tac >>
  simp[Once exec_block_def, Excl "isPREFIX"] >>
  Cases_on `step_inst k C i s` >> simp[Excl "isPREFIX"] >>
  rename1 `step_inst k C i s = OK w` >>
  Cases_on `is_terminator i.inst_opcode`
  >- suspend "term"
  >> suspend "next"
QED

Resume le_coupled_block_OK[term]:
  qpat_x_assum `!m'. _` kall_tac >>
  Cases_on `w.vs_halted` >> simp[Excl "isPREFIX"] >> strip_tac >>
  gvs[Excl "isPREFIX"] >>
  `le_configured_context ctx` by fs[le_round_ready_def] >>
  `load_elim_inst ctx
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
    (df_at NONE (load_analyze ctx fn) bb.bb_label s.vs_inst_idx) i = i` by
    metis_tac[le_configured_terminator_unchanged] >>
  `?v. step_inst k C i t = OK v /\
     le_padded_control {v | isPREFIX "$le_phi_" v} u v` by
    (irule le_coupled_unchanged_term >>
     `padded_exec_equiv {v | isPREFIX "$le_phi_" v} s t` by
       fs[le_body_coupling_def] >>
     `!v. MEM (Var v) i.inst_operands ==> lookup_var v s = lookup_var v t` by
       (rpt strip_tac >> irule le_source_operand_lookup_agreement >>
        fs[le_round_ready_def] >> metis_tac[]) >>
     `i.inst_opcode <> MEMTOP` by
       (fs[le_round_ready_def, EVERY_MEM, fn_insts_def] >>
        metis_tac[o1PassContractTheory.fn_insts_blocks_MEM]) >>
     metis_tac[le_body_coupling_normalize, le_round_ready_def]) >>
  `get_instruction
    (analysis_block_transform_prepend NONE (load_analyze ctx fn)
      (load_phi_prepend (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn))
      (\ll inst. [load_elim_inst ctx
        (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) ll inst]) bb)
    t.vs_inst_idx = SOME i` by metis_tac[le_body_coupling_fetch] >>
  `~v.vs_halted` by fs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def] >>
  qexistsl_tac [`v`, `h`, `i`, `s`] >> simp[Once exec_block_def, Excl "isPREFIX"] >>
  irule le_latest_captures_transformed_step >>
  rule_assum_tac (PURE_REWRITE_RULE [le_round_ready_def, le_body_coupling_def]) >>
  RULE_L_ASSUM_TAC CONJUNCTS >>
  rpt (goal_assum (drule_at Any) >> simp[Excl "isPREFIX"]) >>
  metis_tac[]
QED
Resume le_coupled_block_OK[next]:
  strip_tac >>
  drule_all le_coupled_nonterm_step >> strip_tac >>
  `w.vs_current_bb = s.vs_current_bb` by
    (drule_all step_preserves_control_flow >> simp[]) >>
  `lookup_block (w with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb
     fn.fn_blocks = SOME bb` by simp[] >>
  `?j. get_instruction bb (SUC s.vs_inst_idx) = SOME j` by
    (Cases_on `get_instruction bb (SUC s.vs_inst_idx)` >> simp[] >>
     qpat_x_assum `(if _ then _ else _) = OK u` mp_tac >>
     simp[Once exec_block_def]) >>
  `le_occ_prefix C fn s0 (h ++ [StepOcc bb s.vs_inst_idx k s w]) j
    (w with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule (cj 2 le_occ_prefix_rules) >>
     `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
     fs[get_instruction_def, active_inst_def, Excl "isPREFIX"] >>
     metis_tac[]) >>
  qpat_x_assum `!m'. _`
    (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- fs[get_instruction_def]) >>
  disch_then (qspecl_then
    [`w with vs_inst_idx := SUC s.vs_inst_idx`,
     `h ++ [StepOcc bb s.vs_inst_idx k s w]`,
     `v with vs_inst_idx := SUC t.vs_inst_idx`, `j`, `u`] mp_tac) >>
  simp[Excl "isPREFIX"] >>
  (impl_tac >- gvs[Excl "isPREFIX"]) >> strip_tac >>
  `le_configured_context ctx` by fs[le_round_ready_def] >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
  drule_all le_body_coupling_fetch >> strip_tac >>
  qexistsl_tac [`v'`, `h'`, `j'`, `x`] >>
  simp[Once exec_block_def, le_transformed_nonterm, Excl "isPREFIX"]
QED
Finalise le_coupled_block_OK

Theorem le_configured_terminal_unchanged:
  le_configured_context ctx /\
  (case step_inst k C i s of OK u => F | Error e => F | _ => T) ==>
  load_elim_inst ctx actions ll i = i
Proof
  strip_tac >>
  `MEM i.inst_opcode
    [STOP; RETURN; SINK; SELFDESTRUCT; INVOKE; REVERT; INVALID;
     ASSERT; ASSERT_UNREACHABLE; CREATE; CREATE2; RETURNDATACOPY;
     RET; RETFMP; DRET]` by
    (Cases_on `step_inst k C i s` >> gvs[]
     >- metis_tac[step_inst_halt_opcodes, MEM]
     >- metis_tac[step_inst_abort_opcodes, MEM] >>
     Cases_on `i.inst_opcode = INVOKE` >- simp[] >>
     fs[step_inst_non_invoke] >>
     metis_tac[step_inst_base_intret_opcodes]) >>
  irule loadElimOriginHelpersTheory.load_elim_inst_unchanged >>
  gvs[le_configured_context_def, memory_config_def, storage_config_def,
      transient_config_def, dload_config_def, calldataload_config_def] >>
  gvs[]
QED

Theorem le_coupled_source_step_normalized:
  le_round_ready C fn ctx s0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  le_body_coupling m ctx cfg result actions h bb s t ==>
  (?e. step_inst k C i s = Error e) \/
  lift_result
    (\u v. le_padded_control {v | isPREFIX "$le_phi_" v}
      (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (padded_exec_equiv {v | isPREFIX "$le_phi_" v})
    (padded_exec_equiv {v | isPREFIX "$le_phi_" v})
    (step_inst k C i s) (step_inst k C i t)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM i bb.bb_instructions` by
    (fs[get_instruction_def] >> metis_tac[MEM_EL]) >>
  irule le_padded_source_step_normalized >>
  `!v. MEM (Var v) i.inst_operands ==> lookup_var v s = lookup_var v t` by
    (rpt strip_tac >> irule le_source_operand_lookup_agreement >>
     fs[le_round_ready_def, le_body_coupling_def, Excl "isPREFIX"] >> metis_tac[]) >>
  `i.inst_opcode <> MEMTOP` by
    (fs[le_round_ready_def, EVERY_MEM, fn_insts_def] >>
     metis_tac[o1PassContractTheory.fn_insts_blocks_MEM]) >>
  metis_tac[le_body_coupling_normalize, le_round_ready_def]
QED

Theorem le_coupled_block_terminal:
  !n s h t i r.
  n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
  le_round_ready C fn ctx s0 /\
  le_occ_prefix C fn s0 h i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  le_body_coupling m ctx (cfg_analyze fn) (load_analyze ctx fn)
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) h bb s t /\
  (case r of OK u => F | Error e => F | _ => T) /\
  exec_block k C bb s = r ==>
  lift_result (\u v. F)
    (padded_exec_equiv {v | isPREFIX "$le_phi_" v})
    (padded_exec_equiv {v | isPREFIX "$le_phi_" v}) r
    (exec_block k C
      (analysis_block_transform_prepend NONE (load_analyze ctx fn)
        (load_phi_prepend (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn))
        (\ll inst. [load_elim_inst ctx
          (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) ll inst]) bb) t)
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM i bb.bb_instructions` by
    (fs[get_instruction_def] >> metis_tac[MEM_EL]) >>
  `inst_wf i` by
    (fs[le_round_ready_def] >> metis_tac[fn_inst_wf_every_bb, EVERY_MEM]) >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
  `le_configured_context ctx` by fs[le_round_ready_def] >>
  qpat_x_assum `exec_block k C bb s = r` mp_tac >>
  simp[Once exec_block_def, Excl "isPREFIX"] >>
  Cases_on `step_inst k C i s` >> simp[Excl "isPREFIX"]
  >- suspend "ok" >>
  disch_then (SUBST_ALL_TAC o SYM) >> fs[Excl "isPREFIX"] >>
  `load_elim_inst ctx
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
    (df_at NONE (load_analyze ctx fn) bb.bb_label s.vs_inst_idx) i = i` by
    (irule le_configured_terminal_unchanged >> simp[] >>
     qexistsl_tac [`C`, `k`, `s`] >> simp[]) >>
  drule_all le_body_coupling_fetch >> strip_tac >>
  drule_all le_coupled_source_step_normalized >>
  disch_then (qspec_then `k` mp_tac) >>
  simp[Excl "isPREFIX"] >>
  Cases_on `step_inst k C i t` >>
  simp[lift_result_def, Once exec_block_def, Excl "isPREFIX"]
QED

Resume le_coupled_block_terminal[ok]:
  rename1 `step_inst k C i s = OK w` >>
  Cases_on `is_terminator i.inst_opcode`
  >- (Cases_on `w.vs_halted` >> simp[Excl "isPREFIX"] >>
      disch_then (SUBST_ALL_TAC o SYM) >> fs[Excl "isPREFIX"] >>
      `load_elim_inst ctx
        (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
        (df_at NONE (load_analyze ctx fn) bb.bb_label s.vs_inst_idx) i = i` by
        metis_tac[le_configured_terminator_unchanged] >>
      `?v. step_inst k C i t = OK v /\
        le_padded_control {v | isPREFIX "$le_phi_" v} w v` by
        (irule le_coupled_unchanged_term >>
         `!v. MEM (Var v) i.inst_operands ==> lookup_var v s = lookup_var v t` by
           (rpt strip_tac >> irule le_source_operand_lookup_agreement >>
            fs[le_round_ready_def, le_body_coupling_def, Excl "isPREFIX"] >> metis_tac[]) >>
         `i.inst_opcode <> MEMTOP` by
           (fs[le_round_ready_def, EVERY_MEM, fn_insts_def] >>
            metis_tac[o1PassContractTheory.fn_insts_blocks_MEM]) >>
         metis_tac[le_body_coupling_normalize, le_round_ready_def]) >>
      drule_all le_body_coupling_fetch >> strip_tac >>
      `v.vs_halted` by fs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def] >>
      simp[Once exec_block_def, lift_result_def, Excl "isPREFIX"] >>
      fs[le_padded_control_def]) >>
  simp[Excl "isPREFIX"] >> strip_tac >>
  drule_all le_coupled_nonterm_step >> strip_tac >>
  `w.vs_current_bb = s.vs_current_bb` by
    (drule_all step_preserves_control_flow >> simp[]) >>
  `lookup_block (w with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb
     fn.fn_blocks = SOME bb` by simp[] >>
  `?j. get_instruction bb (SUC s.vs_inst_idx) = SOME j` by
    (Cases_on `get_instruction bb (SUC s.vs_inst_idx)` >> simp[] >>
     `exec_block k C bb (w with vs_inst_idx := SUC s.vs_inst_idx) =
       Error "block not terminated"` by
       (pure_once_rewrite_tac[exec_block_def] >> simp[]) >>
     `r = Error "block not terminated"` by metis_tac[] >>
     fs[Excl "isPREFIX"]) >>
  `le_occ_prefix C fn s0 (h ++ [StepOcc bb s.vs_inst_idx k s w]) j
    (w with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule (cj 2 le_occ_prefix_rules) >>
     fs[get_instruction_def, active_inst_def, Excl "isPREFIX"] >> metis_tac[]) >>
  qpat_x_assum `!m'. _`
    (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- fs[get_instruction_def]) >>
  disch_then (qspecl_then
    [`w with vs_inst_idx := SUC s.vs_inst_idx`,
     `h ++ [StepOcc bb s.vs_inst_idx k s w]`,
     `v with vs_inst_idx := SUC t.vs_inst_idx`, `j`, `r`] mp_tac) >>
  simp[Excl "isPREFIX"] >>
  strip_tac >>
  drule_all le_body_coupling_fetch >> strip_tac >>
  simp[Once exec_block_def, le_transformed_nonterm, Excl "isPREFIX"]
QED
Finalise le_coupled_block_terminal
