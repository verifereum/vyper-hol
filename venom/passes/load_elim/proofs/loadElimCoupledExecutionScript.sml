Theory loadElimCoupledExecution
Ancestors
  loadElimCaptureEntry loadElimCaptureSteps loadElimCaptureInvariant loadElimPrependIndex
  loadElimOccurrenceInvariants loadElimReachedLoad loadElimReachedStore
  loadElimPaddedCalls loadElimPaddedNoncall loadElimMemoryRel
  loadElimActionSelection loadElimLatestJoin loadElimOccurrence loadElimDefs
  loadElimSentinelHelpers cfgAnalysisProps
  venomState venomInst venomExecProps venomExecProofs stateFrame list

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
