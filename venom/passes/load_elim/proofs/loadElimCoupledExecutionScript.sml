Theory loadElimCoupledExecution
Ancestors
  loadElimCaptureEntry loadElimCaptureSteps loadElimCaptureInvariant loadElimPrependIndex
  loadElimReachedLoad loadElimReachedStore
  loadElimPaddedCalls loadElimPaddedNoncall loadElimMemoryRel
  loadElimActionSelection loadElimLatestJoin loadElimOccurrence loadElimDefs
  loadElimSentinelHelpers loadElimKeyShapeInvariant cfgAnalysisProps
  instIdxIndep analysisSimProofsBase venomInstProps contextCodegenRel opcodeClass
  cfgDefs finite_map dfAnalyzeProps memAliasDefs memAliasProps
  venomState venomInst venomExecSemantics venomExecProps venomExecProofs stateFrame stateEquiv list

(* Entry/edge coupling is le_padded_control.  Inside a block only the
   instruction index differs; captures refer to completed source events. *)
Definition le_body_coupling_def:
  le_body_coupling G m ctx cfg result actions h bb s t <=>
    padded_exec_equiv G s t /\
    s.vs_current_bb = t.vs_current_bb /\
    s.vs_prev_bb = t.vs_prev_bb /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH (phis_for_block actions bb.bb_label) /\
    phi_prefix_length bb.bb_instructions <= s.vs_inst_idx /\
    le_latest_captures m ctx cfg result actions h t
End

Theorem le_body_coupling_normalize:
  le_body_coupling G m ctx cfg result actions h bb s t ==>
  le_padded_control G
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
  le_padded_control G p q /\
  le_latest_captures m ctx cfg result actions h q ==>
  le_body_coupling G m ctx cfg result actions h bb
    (p with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    (q with vs_inst_idx := phi_prefix_length bb.bb_instructions +
       LENGTH (phis_for_block actions bb.bb_label))
Proof
  simp[le_body_coupling_def, le_padded_control_def,
       padded_exec_equiv_def, lookup_var_def, read_memory_def,
       execution_frame_def]
QED

Theorem le_body_coupling_increment:
  le_body_coupling G m ctx cfg result actions h bb s t /\
  padded_exec_equiv G u v /\
  u.vs_current_bb = v.vs_current_bb /\ u.vs_prev_bb = v.vs_prev_bb /\
  le_latest_captures m ctx cfg result actions h' v ==>
  le_body_coupling G m ctx cfg result actions h' bb
    (u with vs_inst_idx := SUC s.vs_inst_idx)
    (v with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  simp[le_body_coupling_def, padded_exec_equiv_def,
       lookup_var_def, read_memory_def, execution_frame_def] >>
  decide_tac
QED

(* Static and initial obligations shared by the continuation induction.
   In particular this does not assert a target run or a local simulation. *)
Definition le_round_ready_names_def:
  le_round_ready_names G C fn ctx s0 <=>
    wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
    le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
    (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
    wf_alias_sets ctx.lctx_aliases /\
    fn_entry_label fn = SOME s0.vs_current_bb /\
    is_fixpoint (df_process_block Forward NONE load_join load_transfer
      load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
      (load_analyze ctx fn) /\
    DISJOINT G (set (fn_all_vars fn)) /\
    EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts fn) /\
    EVERY (\f. EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts f)) C.ctx_functions
End

Definition le_round_ready_disjoint_def:
  le_round_ready_disjoint G m C fn ctx s0 <=>
    le_round_ready_names G C fn ctx s0 /\
    (!pa. MEM pa (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) ==>
      pa.pa_phi_out IN G)
End

Definition le_round_ready_def:
  le_round_ready C fn ctx s0 <=>
    le_round_ready_names {v | isPREFIX "$le_phi_" v} C fn ctx s0
End

(* The wrapper's three original alias maps meet every round's query contract,
   independently of that round's source function and configured address space. *)
Theorem le_function_alias_maps_wf:
  wf_alias_sets (memory_alias_analyze bp fn) /\
  wf_alias_sets (storage_alias_analyze bp fn) /\
  wf_alias_sets (transient_alias_analyze bp fn)
Proof
  simp[memory_alias_analyze_def, storage_alias_analyze_def,
       transient_alias_analyze_def, memAliasPropsTheory.ma_analyze_wf]
QED

Theorem le_body_coupling_fetch:
  le_configured_context ctx /\
  le_body_coupling G m ctx cfg result actions h bb s t /\
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
  le_round_ready_disjoint G m C fn ctx s0 /\
  le_occ_prefix C fn s0 h i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  le_body_coupling G m ctx (cfg_analyze fn) (load_analyze ctx fn)
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) h bb s t /\
  inst_wf i /\ step_inst k C i s = OK s' /\
  phi_action_lookup
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
    i.inst_id = SOME out ==>
  ?t'. step_inst k C
    (load_elim_inst ctx
      (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
      (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx) i) t = OK t' /\
    padded_exec_equiv G s' t' /\
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
  rule_assum_tac (PURE_REWRITE_RULE [le_round_ready_disjoint_def, le_round_ready_names_def, le_body_coupling_def]) >>
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
  simp[Excl "isPREFIX"] >> metis_tac[]
QED

Theorem le_source_operand_lookup_agreement:
  MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\
  DISJOINT G (set (fn_all_vars fn)) /\
  padded_exec_equiv G s t ==>
  !v. MEM (Var v) i.inst_operands ==> lookup_var v s = lookup_var v t
Proof
  rpt strip_tac >>
  `MEM v (fn_all_vars fn)` by
    metis_tac[cfgNormBaseTheory.inst_operand_var_in_fn_all_vars] >>
  `v NOTIN G` by
    (fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
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
  le_round_ready_disjoint G m C fn ctx s0 /\
  le_occ_prefix C fn s0 h i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  le_body_coupling G m ctx (cfg_analyze fn) (load_analyze ctx fn)
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) h bb s t /\
  inst_wf i /\ step_inst k C i s = OK s' /\
  load_elim_inst ctx
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx) i <> i ==>
  ?t'. step_inst k C
    (load_elim_inst ctx
      (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
      (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx) i) t = OK t' /\
    padded_exec_equiv G s' t' /\
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
  >- (rule_assum_tac (PURE_REWRITE_RULE [le_round_ready_disjoint_def, le_round_ready_names_def, le_body_coupling_def]) >>
      RULE_L_ASSUM_TAC CONJUNCTS >>
      irule le_reached_singleton_load_replacement >>
      simp[Excl "isPREFIX"] >>
      rpt (goal_assum (drule_at Any) >> simp[Excl "isPREFIX"]))
  >- (irule le_coupled_captured_load >>
      rpt (goal_assum (drule_at Any) >> simp[Excl "isPREFIX"])) >>
  rule_assum_tac (PURE_REWRITE_RULE [le_round_ready_disjoint_def, le_round_ready_names_def, le_body_coupling_def]) >>
  RULE_L_ASSUM_TAC CONJUNCTS >>
  irule le_reached_store_replacement >>
  simp[Excl "isPREFIX"] >>
  rpt (goal_assum (drule_at Any) >> simp[Excl "isPREFIX"])
QED

Theorem le_coupled_source_nonterm:
  le_round_ready_disjoint G m C fn ctx s0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  le_body_coupling G m ctx cfg result actions h bb s t /\
  ~is_terminator i.inst_opcode /\ step_inst k C i s = OK u ==>
  ?v. step_inst k C i t = OK v /\
    padded_exec_equiv G u v /\
    u.vs_current_bb = v.vs_current_bb /\ u.vs_prev_bb = v.vs_prev_bb /\
    u.vs_inst_idx = s.vs_inst_idx /\ v.vs_inst_idx = t.vs_inst_idx
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM i bb.bb_instructions` by
    (fs[get_instruction_def] >> metis_tac[MEM_EL]) >>
  `le_padded_control G
     (s with vs_inst_idx := 0) (t with vs_inst_idx := 0)` by
    metis_tac[le_body_coupling_normalize] >>
  rule_assum_tac (PURE_REWRITE_RULE [le_round_ready_disjoint_def, le_round_ready_names_def, le_body_coupling_def]) >>
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
  le_round_ready_disjoint G m C fn ctx s0 /\
  le_occ_prefix C fn s0 h i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  le_body_coupling G m ctx (cfg_analyze fn) (load_analyze ctx fn)
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) h bb s t /\
  inst_wf i /\ ~is_terminator i.inst_opcode /\ step_inst k C i s = OK u ==>
  ?v. step_inst k C
    (load_elim_inst ctx
      (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
      (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx) i) t = OK v /\
    le_body_coupling G m ctx (cfg_analyze fn) (load_analyze ctx fn)
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
    padded_exec_equiv G u v /\
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
  rule_assum_tac (PURE_REWRITE_RULE [le_round_ready_disjoint_def, le_round_ready_names_def, le_body_coupling_def]) >>
  RULE_L_ASSUM_TAC CONJUNCTS >>
  rpt (goal_assum (drule_at Any) >> simp[Excl "isPREFIX"]) >>
  metis_tac[]
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
  le_round_ready_disjoint G m C fn ctx s0 /\
  le_occ_prefix C fn s0 h i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  le_body_coupling G m ctx (cfg_analyze fn) (load_analyze ctx fn)
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) h bb s t /\
  exec_block k C bb s = OK u ==>
  ?v h' j x.
    exec_block k C
      (analysis_block_transform_prepend NONE (load_analyze ctx fn)
        (load_phi_prepend (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn))
        (\ll inst. [load_elim_inst ctx
          (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) ll inst]) bb) t = OK v /\
    le_padded_control G u v /\
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
    (fs[le_round_ready_disjoint_def, le_round_ready_names_def] >> metis_tac[fn_inst_wf_every_bb, EVERY_MEM]) >>
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
  `le_configured_context ctx` by fs[le_round_ready_disjoint_def, le_round_ready_names_def] >>
  `load_elim_inst ctx
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
    (df_at NONE (load_analyze ctx fn) bb.bb_label s.vs_inst_idx) i = i` by
    metis_tac[le_configured_terminator_unchanged] >>
  `?v. step_inst k C i t = OK v /\
     le_padded_control G u v` by
    (irule le_coupled_unchanged_term >>
     `padded_exec_equiv G s t` by
       fs[le_body_coupling_def] >>
     `!v. MEM (Var v) i.inst_operands ==> lookup_var v s = lookup_var v t` by
       (rpt strip_tac >> irule le_source_operand_lookup_agreement >>
        fs[le_round_ready_disjoint_def, le_round_ready_names_def] >> metis_tac[]) >>
     `i.inst_opcode <> MEMTOP` by
       (fs[le_round_ready_disjoint_def, le_round_ready_names_def, EVERY_MEM, fn_insts_def] >>
        metis_tac[o1PassContractTheory.fn_insts_blocks_MEM]) >>
     metis_tac[le_body_coupling_normalize, le_round_ready_disjoint_def, le_round_ready_names_def]) >>
  `get_instruction
    (analysis_block_transform_prepend NONE (load_analyze ctx fn)
      (load_phi_prepend (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn))
      (\ll inst. [load_elim_inst ctx
        (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) ll inst]) bb)
    t.vs_inst_idx = SOME i` by metis_tac[le_body_coupling_fetch] >>
  `~v.vs_halted` by fs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def] >>
  qexistsl_tac [`v`, `h`, `i`, `s`] >> simp[Once exec_block_def, Excl "isPREFIX"] >>
  irule le_latest_captures_transformed_step >>
  rule_assum_tac (PURE_REWRITE_RULE [le_round_ready_disjoint_def, le_round_ready_names_def, le_body_coupling_def]) >>
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
  `le_configured_context ctx` by fs[le_round_ready_disjoint_def, le_round_ready_names_def] >>
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
  le_round_ready_disjoint G m C fn ctx s0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  le_body_coupling G m ctx cfg result actions h bb s t ==>
  (?e. step_inst k C i s = Error e) \/
  lift_result
    (\u v. le_padded_control G
      (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (padded_exec_equiv G)
    (padded_exec_equiv G)
    (step_inst k C i s) (step_inst k C i t)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM i bb.bb_instructions` by
    (fs[get_instruction_def] >> metis_tac[MEM_EL]) >>
  irule le_padded_source_step_normalized >>
  `!v. MEM (Var v) i.inst_operands ==> lookup_var v s = lookup_var v t` by
    (rpt strip_tac >> irule le_source_operand_lookup_agreement >>
     fs[le_round_ready_disjoint_def, le_round_ready_names_def, le_body_coupling_def, Excl "isPREFIX"] >> metis_tac[]) >>
  `i.inst_opcode <> MEMTOP` by
    (fs[le_round_ready_disjoint_def, le_round_ready_names_def, EVERY_MEM, fn_insts_def] >>
     metis_tac[o1PassContractTheory.fn_insts_blocks_MEM]) >>
  metis_tac[le_body_coupling_normalize, le_round_ready_disjoint_def, le_round_ready_names_def]
QED

Theorem le_coupled_block_terminal:
  !n s h t i r.
  n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
  le_round_ready_disjoint G m C fn ctx s0 /\
  le_occ_prefix C fn s0 h i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  le_body_coupling G m ctx (cfg_analyze fn) (load_analyze ctx fn)
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) h bb s t /\
  (case r of OK u => F | Error e => F | _ => T) /\
  exec_block k C bb s = r ==>
  lift_result (\u v. F)
    (padded_exec_equiv G)
    (padded_exec_equiv G) r
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
    (fs[le_round_ready_disjoint_def, le_round_ready_names_def] >> metis_tac[fn_inst_wf_every_bb, EVERY_MEM]) >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
  `le_configured_context ctx` by fs[le_round_ready_disjoint_def, le_round_ready_names_def] >>
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
        le_padded_control G w v` by
        (irule le_coupled_unchanged_term >>
         `!v. MEM (Var v) i.inst_operands ==> lookup_var v s = lookup_var v t` by
           (rpt strip_tac >> irule le_source_operand_lookup_agreement >>
            fs[le_round_ready_disjoint_def, le_round_ready_names_def, le_body_coupling_def, Excl "isPREFIX"] >> metis_tac[]) >>
         `i.inst_opcode <> MEMTOP` by
           (fs[le_round_ready_disjoint_def, le_round_ready_names_def, EVERY_MEM, fn_insts_def] >>
            metis_tac[o1PassContractTheory.fn_insts_blocks_MEM]) >>
         metis_tac[le_body_coupling_normalize, le_round_ready_disjoint_def, le_round_ready_names_def]) >>
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

(* PHI entry consumes a source occurrence, never a successful target run. *)
Theorem le_coupled_phi_entry:
  le_round_ready_disjoint G m C fn ctx s0 /\
  le_occ_prefix C fn s0 (h ++ [PhiOcc bb u p]) i
    (p with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
  le_padded_control G u r /\
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) bb.bb_label) /\
  le_latest_captures m ctx (cfg_analyze fn) (load_analyze ctx fn)
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) h r ==>
  ?q. eval_phis r
    (analysis_block_transform_prepend NONE (load_analyze ctx fn)
      (load_phi_prepend (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn))
      (\ll inst. [load_elim_inst ctx
        (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) ll inst]) bb).bb_instructions = OK q /\
    le_body_coupling G m ctx (cfg_analyze fn) (load_analyze ctx fn)
      (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
      (h ++ [PhiOcc bb u p]) bb
      (p with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      (q with vs_inst_idx := phi_prefix_length bb.bb_instructions +
        LENGTH (phis_for_block
          (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) bb.bb_label))
Proof
  strip_tac >>
  `r.vs_prev_bb = u.vs_prev_bb /\ r.vs_labels = u.vs_labels` by
    fs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def] >>
  rule_assum_tac (PURE_REWRITE_RULE [le_round_ready_disjoint_def, le_round_ready_names_def, le_padded_control_def]) >>
  RULE_L_ASSUM_TAC CONJUNCTS >>
  drule_all le_occ_prefix_actual_phis_captures >>
  strip_tac >> qexists_tac `q` >> conj_tac >- first_assum ACCEPT_TAC >>
  irule le_body_coupling_enter >> conj_tac
  >- (drule loadElimOccurrenceInversionTheory.le_occ_prefix_phi_semantics >> strip_tac >>
      qpat_x_assum `eval_phis u _ = OK p` mp_tac >>
      rewrite_tac[loadElimOperationalHistoryTheory.le_eval_phis_snapshot] >> strip_tac >>
      drule loadElimActualPhiFrameTheory.le_snapshot_batch_controls >> strip_tac >>
      fs[le_padded_control_def, Excl "isPREFIX"]) >>
  first_assum ACCEPT_TAC
QED

Theorem le_pred_insert_distinct[local]:
  !xs acc pred.
    (!lbl. ALL_DISTINCT (fmap_lookup_list acc lbl)) ==>
    !lbl. ALL_DISTINCT (fmap_lookup_list
      (FOLDR (\succ m2. m2 |+ (succ,
        ordered_set_insert pred (fmap_lookup_list m2 succ))) acc xs) lbl)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`acc`, `pred`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[cfgHelpersTheory.fmap_lookup_list_update] >>
  IF_CASES_TAC >> simp[] >>
  qmatch_goalsub_abbrev_tac `ordered_set_insert pred ys` >>
  `ALL_DISTINCT ys` by metis_tac[] >>
  simp[ordered_set_insert_def] >>
  IF_CASES_TAC >> simp[ALL_DISTINCT_APPEND]
QED

Theorem le_build_preds_distinct[local]:
  !bbs acc.
    (!lbl. ALL_DISTINCT (fmap_lookup_list acc lbl)) ==>
    !lbl. ALL_DISTINCT (fmap_lookup_list
      (FOLDL (\m bb. FOLDR (\succ m2. m2 |+ (succ,
        ordered_set_insert bb.bb_label (fmap_lookup_list m2 succ)))
        m (fmap_lookup_list succs bb.bb_label)) acc bbs) lbl)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> irule le_pred_insert_distinct >> simp[]
QED

Theorem le_cfg_preds_distinct:
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) lbl)
Proof
  simp[cfg_preds_of_def, cfg_analyze_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[build_preds_def] >> irule le_build_preds_distinct >>
  simp[init_preds_def, fmap_lookup_list_def] >> rpt strip_tac >>
  CASE_TAC >> simp[] >>
  qspecl_then [`MAP (\bb. bb.bb_label) fn.fn_blocks`, `[]`, `lbl`, `x`]
    mp_tac dfAnalyzePropsTheory.foldl_fempty_val >>
  simp[rich_listTheory.FOLDL_MAP]
QED

(* The source entry certificate is supplied by start or by the last completed
   terminator; it mentions no target execution. *)
Theorem le_coupled_run:
  !fuel u h t.
  le_round_ready_disjoint G m C fn ctx s0 /\
  (!bb p i. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis u bb.bb_instructions = OK p /\
    get_instruction bb (phi_prefix_length bb.bb_instructions) = SOME i ==>
    le_occ_prefix C fn s0 (h ++ [PhiOcc bb u p]) i
      (p with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
  le_padded_control G u t /\
  le_latest_captures m ctx (cfg_analyze fn) (load_analyze ctx fn)
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) h t ==>
  (?e. run_blocks fuel C fn u = Error e) \/
  lift_result (le_padded_control G)
    (padded_exec_equiv G)
    (padded_exec_equiv G)
    (run_blocks fuel C fn u)
    (run_blocks fuel C
      (analysis_function_transform_prepend NONE (load_analyze ctx fn)
        (load_phi_prepend (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn))
        (\ll inst. [load_elim_inst ctx
          (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) ll inst]) fn) t)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- simp[Once run_blocks_def] >>
  Cases_on `lookup_block u.vs_current_bb fn.fn_blocks`
  >- simp[Once run_blocks_def] >>
  rename1 `lookup_block u.vs_current_bb fn.fn_blocks = SOME bb` >>
  reverse (qspec_then `u` (qspec_then `bb.bb_instructions` strip_assume_tac)
    eval_phis_ok_or_error_defs)
  >- simp[Once run_blocks_def] >>
  rename1 `eval_phis u bb.bb_instructions = OK p` >>
  Cases_on `get_instruction bb (phi_prefix_length bb.bb_instructions)`
  >- (disj1_tac >> pure_once_rewrite_tac[run_blocks_def] >>
      simp[] >> pure_once_rewrite_tac[exec_block_def] >> simp[]) >>
  rename1 `get_instruction bb (phi_prefix_length bb.bb_instructions) = SOME i` >>
  `le_occ_prefix C fn s0 (h ++ [PhiOcc bb u p]) i
    (p with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by metis_tac[] >>
  `?q. eval_phis t
    (analysis_block_transform_prepend NONE (load_analyze ctx fn)
      (load_phi_prepend (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn))
      (\ll inst. [load_elim_inst ctx
        (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) ll inst]) bb).bb_instructions = OK q /\
    le_body_coupling G m ctx (cfg_analyze fn) (load_analyze ctx fn)
      (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
      (h ++ [PhiOcc bb u p]) bb
      (p with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      (q with vs_inst_idx := phi_prefix_length bb.bb_instructions +
        LENGTH (phis_for_block
          (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) bb.bb_label))` by
    (irule le_coupled_phi_entry >> simp[le_cfg_preds_distinct] >> metis_tac[]) >>
  `p.vs_current_bb = u.vs_current_bb` by
    (qpat_x_assum `eval_phis u _ = OK p` mp_tac >>
     rewrite_tac[loadElimOperationalHistoryTheory.le_eval_phis_snapshot] >>
     strip_tac >> drule loadElimActualPhiFrameTheory.le_snapshot_batch_controls >> simp[]) >>
  `t.vs_current_bb = u.vs_current_bb` by fs[le_padded_control_def] >>
  `le_configured_context ctx` by fs[le_round_ready_disjoint_def, le_round_ready_names_def] >>
  qmatch_asmsub_abbrev_tac `eval_phis t bt.bb_instructions` >>
  `lookup_block t.vs_current_bb
    (analysis_function_transform_prepend NONE (load_analyze ctx fn)
      (load_phi_prepend (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn))
      (\ll inst. [load_elim_inst ctx
        (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) ll inst]) fn).fn_blocks = SOME bt` by
    simp[analysisSimDefsTheory.analysis_function_transform_prepend_def,
      passSimulationDefsTheory.function_map_transform_def,
      passSimulationPropsTheory.lookup_block_map,
      analysisSimDefsTheory.analysis_block_transform_prepend_def, Abbr `bt`] >>
  Cases_on `exec_block fuel C bb
    (p with vs_inst_idx := phi_prefix_length bb.bb_instructions)`
  >- suspend "exit"
  >- suspend "halt"
  >- suspend "abort"
  >- suspend "intret"
  >> (disj1_tac >> pure_once_rewrite_tac[run_blocks_def] >> simp[])
QED

Resume le_coupled_run[exit]:
  drule_at (Pat `le_body_coupling _ _ _ _ _ _ _ _ _ _`) le_coupled_block_OK >>
  simp[Excl "isPREFIX"] >>
  disch_then (qspecl_then [`s0`, `fuel`, `C`] mp_tac) >>
  simp[Excl "isPREFIX"] >> strip_tac >>
  `!nb pp jj. lookup_block v.vs_current_bb fn.fn_blocks = SOME nb /\
      eval_phis v nb.bb_instructions = OK pp /\
      get_instruction nb (phi_prefix_length nb.bb_instructions) = SOME jj ==>
      le_occ_prefix C fn s0
        ((h' ++ [StepOcc bb x.vs_inst_idx fuel x v]) ++ [PhiOcc nb v pp]) jj
        (pp with vs_inst_idx := phi_prefix_length nb.bb_instructions)` by
    (rpt strip_tac >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     irule (cj 3 le_occ_prefix_rules) >>
     simp[active_inst_def, get_instruction_def, Excl "isPREFIX"] >>
     fs[get_instruction_def, Excl "isPREFIX"] >>
     qpat_x_assum `eval_phis v _ = OK pp` mp_tac >>
     rewrite_tac[loadElimOperationalHistoryTheory.le_eval_phis_snapshot] >>
     strip_tac >> drule loadElimActualPhiFrameTheory.le_snapshot_batch_controls >>
     simp[Excl "isPREFIX"] >> strip_tac >>
     qexists_tac `nb` >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `~v'.vs_halted` by
    fs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def] >>
  first_x_assum (qspecl_then [`v`, `h' ++ [StepOcc bb x.vs_inst_idx fuel x v]`, `v'`] mp_tac) >>
  simp[Excl "isPREFIX"] >> strip_tac >>
  pure_once_rewrite_tac[run_blocks_def] >>
  simp[le_actual_prepend_phi_length, Abbr `bt`, Excl "isPREFIX"]
QED
Resume le_coupled_run[halt]:
  drule_at (Pat `le_body_coupling _ _ _ _ _ _ _ _ _ _`) le_coupled_block_terminal >>
  simp[Excl "isPREFIX"] >>
  disch_then (qspecl_then [`s0`, `fuel`, `C`] mp_tac) >>
  simp[Excl "isPREFIX"] >> strip_tac >>
  disj2_tac >> pure_once_rewrite_tac[run_blocks_def] >>
  simp[le_actual_prepend_phi_length, Abbr `bt`, Excl "isPREFIX"] >>
  qmatch_asmsub_abbrev_tac `lift_result _ _ _ _ br` >>
  Cases_on `br` >> gvs[lift_result_def, Excl "isPREFIX"]
QED
Resume le_coupled_run[abort]:
  drule_at (Pat `le_body_coupling _ _ _ _ _ _ _ _ _ _`) le_coupled_block_terminal >>
  simp[Excl "isPREFIX"] >>
  disch_then (qspecl_then [`s0`, `fuel`, `C`] mp_tac) >>
  simp[Excl "isPREFIX"] >> strip_tac >>
  disj2_tac >> pure_once_rewrite_tac[run_blocks_def] >>
  simp[le_actual_prepend_phi_length, Abbr `bt`, Excl "isPREFIX"] >>
  qmatch_asmsub_abbrev_tac `lift_result _ _ _ _ br` >>
  Cases_on `br` >> gvs[lift_result_def, Excl "isPREFIX"]
QED
Resume le_coupled_run[intret]:
  drule_at (Pat `le_body_coupling _ _ _ _ _ _ _ _ _ _`) le_coupled_block_terminal >>
  simp[Excl "isPREFIX"] >>
  disch_then (qspecl_then [`s0`, `fuel`, `C`] mp_tac) >>
  simp[Excl "isPREFIX"] >> strip_tac >>
  disj2_tac >> pure_once_rewrite_tac[run_blocks_def] >>
  simp[le_actual_prepend_phi_length, Abbr `bt`, Excl "isPREFIX"] >>
  qmatch_asmsub_abbrev_tac `lift_result _ _ _ _ br` >>
  Cases_on `br` >> gvs[lift_result_def, Excl "isPREFIX"]
QED
Finalise le_coupled_run

Theorem le_coupled_run_initial_disjoint:
  le_round_ready_disjoint G m C fn ctx s0 /\
  le_padded_control G s0 t ==>
  (?e. run_blocks fuel C fn s0 = Error e) \/
  lift_result (le_padded_control G)
    (padded_exec_equiv G)
    (padded_exec_equiv G)
    (run_blocks fuel C fn s0)
    (run_blocks fuel C
      (analysis_function_transform_prepend NONE (load_analyze ctx fn)
        (load_phi_prepend (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn))
        (\ll inst. [load_elim_inst ctx
          (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) ll inst]) fn) t)
Proof
  strip_tac >> irule le_coupled_run >> simp[Excl "isPREFIX"] >>
  qexistsl_tac [`[]`, `s0`] >>
  simp[Excl "isPREFIX"] >> rpt strip_tac >>
  irule (cj 1 le_occ_prefix_rules) >> simp[active_inst_def] >>
  qpat_x_assum `eval_phis s0 _ = OK p` mp_tac >>
  rewrite_tac[loadElimOperationalHistoryTheory.le_eval_phis_snapshot] >>
  strip_tac >> drule loadElimActualPhiFrameTheory.le_snapshot_batch_controls >>
  simp[Excl "isPREFIX"] >> strip_tac >>
  fs[get_instruction_def, Excl "isPREFIX"] >>
  qexists_tac `bb` >> metis_tac[lookup_block_MEM, lookup_block_label]
QED

(* Compatibility export: the reserved-prefix contract is a specialization,
   not a separate execution induction. *)
Theorem le_coupled_run_initial:
  le_round_ready C fn ctx s0 /\
  le_padded_control {v | isPREFIX "$le_phi_" v} s0 t ==>
  (?e. run_blocks fuel C fn s0 = Error e) \/
  lift_result (le_padded_control {v | isPREFIX "$le_phi_" v})
    (padded_exec_equiv {v | isPREFIX "$le_phi_" v})
    (padded_exec_equiv {v | isPREFIX "$le_phi_" v})
    (run_blocks fuel C fn s0)
    (run_blocks fuel C
      (analysis_function_transform_prepend NONE (load_analyze ctx fn)
        (load_phi_prepend (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn))
        (\ll inst. [load_elim_inst ctx
          (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) ll inst]) fn) t)
Proof
  strip_tac >> irule le_coupled_run_initial_disjoint >>
  fs[le_round_ready_def, le_round_ready_disjoint_def, Excl "isPREFIX"] >>
  metis_tac[loadElimActionFreshnessTheory.le_collected_action_output_prefix]
QED
