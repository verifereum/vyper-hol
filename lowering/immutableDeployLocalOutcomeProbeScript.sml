(* Exhaustive counted-outcome audit for the certified local fixture. *)
Theory immutableDeployLocalOutcomeProbe
Ancestors
  immutableDeployLocalEndpointProbe immutableDeployLocalCodeProbe
  fragGasPath gasOutcome gasExemptCert gasSummary vyperState

Theorem local_probe_no_exempt_outcome:
  !memory tops ctx func s0 marks err ee leaf finish.
    ~gas_exempt_cert memory tops (ctx,func)
      (ignore_bind (eval_stmt local_probe_cx local_probe_empty_stmt) (return ()))
      (local_probe_es,s0) marks (err,ee) (leaf,finish)
Proof
  rpt strip_tac >> drule gas_exempt_cert_execution >>
  simp[ignore_bind_def, bind_def, local_probe_eval_stmt, return_def]
QED

Theorem local_probe_summary_source_result:
  !memory ctx func s0 marks res ee r.
    gas_marked_exec memory (ctx,func)
      (eval_stmt local_probe_cx local_probe_empty_stmt)
      (local_probe_es,s0) marks res ee r ==>
    res = INL () /\ ee with gas_obs := [] = local_probe_es with gas_obs := []
Proof
  rpt gen_tac >> simp[gas_marked_exec_def, local_probe_eval_stmt] >>
  strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >>
  strip_tac >> simp[] >>
  qpat_x_assum `_ = ee with gas_obs := []`
    (mp_tac o Q.AP_TERM `\st. st with gas_obs := []`) >> simp[]
QED

Theorem local_probe_prefix_control:
  local_probe_entry.vs_current_bb = "__deploy" /\
  local_probe_entry.vs_inst_idx = 3 /\ ~local_probe_entry.vs_halted /\
  local_probe_after_load.vs_current_bb = "__deploy" /\
  local_probe_after_load.vs_inst_idx = 4 /\ ~local_probe_after_load.vs_halted /\
  local_probe_after_add.vs_current_bb = "__deploy" /\
  local_probe_after_add.vs_inst_idx = 5 /\ ~local_probe_after_add.vs_halted /\
  local_probe_after_store.vs_current_bb = "__deploy" /\
  local_probe_after_store.vs_inst_idx = 6 /\ ~local_probe_after_store.vs_halted
Proof
  EVAL_TAC
QED

Theorem local_probe_prefix_edges:
  !ctx n r.
    (gas_path_edge ctx local_probe_fn local_probe_entry n r <=>
       n = 0 /\ r = OK local_probe_after_load) /\
    (gas_path_edge ctx local_probe_fn local_probe_after_load n r <=>
       n = 0 /\ r = OK local_probe_after_add) /\
    (gas_path_edge ctx local_probe_fn local_probe_after_add n r <=>
       n = 0 /\ r = OK local_probe_after_store)
Proof
  rpt gen_tac >> rewrite_tac[gas_path_edge_def] >>
  simp[local_probe_prefix_control, local_probe_fn_shape,
    venomInstTheory.mk_raw_function_def,
    venomInstTheory.lookup_block_def,
    venomInstTheory.get_instruction_def, listTheory.FIND_thm,
    venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
    local_probe_assignment_steps, fragExecTheory.exit_result_def,
    gasCountTheory.gas_count_step_def] >>
  simp[SRULE [venomInstTheory.mk_inst_def] local_probe_assignment_steps,
    venomStateTheory.update_var_def, venomExecSemanticsTheory.istore_def,
    venomStateTheory.mstore_def, local_probe_prefix_control,
    fragExecTheory.exit_result_def, local_probe_after_load_def,
    local_probe_after_add_def, local_probe_after_store_def]
QED

Theorem return_step_never_ok:
  !fuel ctx inst s t. inst.inst_opcode = RETURN ==>
    step_inst fuel ctx inst s <> OK t
Proof
  rpt gen_tac >> strip_tac >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
    Once venomExecSemanticsTheory.step_inst_base_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `h::ops` >> Cases_on `ops` >> simp[] >>
  rename1 `h::h'::ops'` >> Cases_on `ops'` >> simp[] >>
  rpt CASE_TAC >> simp[]
QED

Theorem local_probe_suffix_edge_control:
  !ctx s n t.
    s.vs_current_bb = "@ctor_exit_0" /\
    gas_path_edge ctx local_probe_fn s n (OK t) ==>
    t.vs_current_bb = "@ctor_exit_0"
Proof
  rpt gen_tac >> rewrite_tac[gas_path_edge_def] >> strip_tac >>
  gvs[local_probe_fn_shape, venomInstTheory.mk_raw_function_def,
    venomInstTheory.lookup_block_def, listTheory.FIND_thm,
    venomInstTheory.get_instruction_def]
  >- metis_tac[venomInstProofsTheory.step_preserves_control_flow] >>
  `s.vs_inst_idx = 0 \/ s.vs_inst_idx = 1 \/ s.vs_inst_idx = 2 \/
   s.vs_inst_idx = 3 \/ s.vs_inst_idx = 4` by decide_tac >>
  gvs[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  gvs[fragExecTheory.exit_result_def] >>
  gvs[return_step_never_ok] >>
  qpat_x_assum `OK _ = step_inst _ _ _ _` (assume_tac o SYM) >>
  gvs[fragExecTheory.exit_result_def]
QED

Theorem local_probe_suffix_path_control:
  !ctx s n r. gas_path ctx local_probe_fn s n r ==>
    !t. s.vs_current_bb = "@ctor_exit_0" /\ r = OK t ==>
      t.vs_current_bb = "@ctor_exit_0"
Proof
  `!ctx fn s n r. gas_path ctx fn s n r ==>
    fn = local_probe_fn ==> !t.
      s.vs_current_bb = "@ctor_exit_0" /\ r = OK t ==>
      t.vs_current_bb = "@ctor_exit_0"` suffices_by metis_tac[] >>
  ho_match_mp_tac gas_path_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[])
  >- (rpt strip_tac >> gvs[] >>
      metis_tac[local_probe_suffix_edge_control]) >>
  rpt strip_tac >> gvs[fragExecTheory.exit_result_def]
QED

Theorem local_probe_store_edge_control:
  !ctx n t. gas_path_edge ctx local_probe_fn local_probe_after_store n (OK t) ==>
    t.vs_current_bb = "@ctor_exit_0"
Proof
  rpt gen_tac >> rewrite_tac[gas_path_edge_def] >>
  simp[local_probe_prefix_control, local_probe_fn_shape,
    venomInstTheory.mk_raw_function_def, venomInstTheory.lookup_block_def,
    listTheory.FIND_thm, venomInstTheory.get_instruction_def] >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
    venomInstTheory.mk_inst_def, venomExecProofsTheory.step_jmp_behavior,
    venomInstTheory.is_terminator_def, venomStateTheory.jump_to_def,
    fragExecTheory.exit_result_def] >>
  simp[venomExecSemanticsTheory.eval_phis_def,
    venomExecSemanticsTheory.phi_prefix_length_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem local_probe_normal_path_classification:
  !ctx s n r. gas_path ctx local_probe_fn s n r ==>
    !t. r = OK t ==>
      (s = local_probe_entry \/ s = local_probe_after_load \/
       s = local_probe_after_add \/ s = local_probe_after_store \/
       s.vs_current_bb = "@ctor_exit_0") ==>
      t = local_probe_entry \/ t = local_probe_after_load \/
      t = local_probe_after_add \/ t = local_probe_after_store \/
      t.vs_current_bb = "@ctor_exit_0"
Proof
  `!ctx fn s n r. gas_path ctx fn s n r ==> fn = local_probe_fn ==>
    !t. r = OK t ==>
      (s = local_probe_entry \/ s = local_probe_after_load \/
       s = local_probe_after_add \/ s = local_probe_after_store \/
       s.vs_current_bb = "@ctor_exit_0") ==>
      t = local_probe_entry \/ t = local_probe_after_load \/
      t = local_probe_after_add \/ t = local_probe_after_store \/
      t.vs_current_bb = "@ctor_exit_0"` suffices_by metis_tac[] >>
  ho_match_mp_tac gas_path_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[])
  >- (rpt strip_tac >> gvs[] >>
      gvs[local_probe_prefix_edges, local_probe_store_edge_control,
        local_probe_suffix_edge_control] >>
      metis_tac[local_probe_store_edge_control, local_probe_suffix_edge_control]) >>
  rpt strip_tac >> gvs[fragExecTheory.exit_result_def]
QED

Theorem local_probe_normal_landing:
  !ctx n t sb.
    gas_path ctx local_probe_fn local_probe_entry n (OK t) /\
    sb = SND (stmt_env local_probe_empty_ce NoLoop NoneT
      local_probe_empty_stmt local_probe_sa) /\
    stmt_lands NoLoop sb (INL ()) t ==>
    t = local_probe_after_store
Proof
  rpt strip_tac >> drule local_probe_normal_path_classification >>
  disch_then (qspec_then `t` mp_tac) >> simp[] >>
  strip_tac >> gvs[loweringPostsTheory.stmt_lands_def,
    local_probe_assignment_shape, local_probe_sa_shape,
    local_probe_prefix_control,
    immutableDeployEmptyAssignedCodeTheory.assigned_immutable_sa_def,
    vyperCompilerTheory.initial_compile_state_def]
QED

Theorem local_probe_no_counted_outcome:
  ~gas_outcome F (cx_tops local_probe_cx)
    (local_probe_unit.cu_context,local_probe_fn)
    (eval_stmt local_probe_cx local_probe_empty_stmt)
    (local_probe_es,local_probe_entry)
    (stmt_post local_probe_unit.cu_context local_probe_fn local_probe_cx NoLoop
      local_probe_empty_ce local_probe_empty_ce local_probe_sa
      (SND (stmt_env local_probe_empty_ce NoLoop NoneT local_probe_empty_stmt local_probe_sa))
      local_probe_entry)
    (\res ee r. !tail. stmt_exit (\v es r. F) (ee with gas_obs := tail) res r)
Proof
  rewrite_tac[gas_outcome_def] >> reverse strip_tac
  >- metis_tac[local_probe_no_exempt_outcome] >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_summary_at_def] >>
  strip_tac >> drule local_probe_summary_source_result >> strip_tac >> gvs[]
  >- (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_marked_exec_def] >> strip_tac >>
      drule fragGasModeTheory.gas_marked_path_exec >> strip_tac >>
      `t = local_probe_after_store` by
        (irule local_probe_normal_landing >>
         reverse conj_tac >- metis_tac[] >>
         qpat_x_assum `stmt_post _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
         simp[stmtSimDefsTheory.stmt_post_def] >> metis_tac[]) >>
      gvs[local_probe_endpoint_no_post]) >>
  qpat_x_assum `!tail. stmt_exit _ _ _ _` (qspec_then `[]` mp_tac) >>
  simp[stmtSimDefsTheory.stmt_exit_def, exprSimDefsTheory.expr_exit_def]
QED
