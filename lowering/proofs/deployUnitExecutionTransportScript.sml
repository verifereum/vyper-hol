(* Restricted raw-FMP transport at the deployment certificate boundary. *)
Theory deployUnitExecutionTransport
Ancestors
  deployUnitExecution rawFmpTransport ptrSafeFmpTransport fragGasOriginFmpTransport
  rawFmpRecursiveTransport unitShapeDefs ctorDeployDefs venomExecSemantics
  venomState venomInst ptrDiscipline fragGasOrigin fragGasOriginPtr list ptrSafeRun
  createSizeExit

Theorem deploy_venom_result_rel_raw_fmp_transport:
  raw_fmp_result_rel p i e r r' /\
  deploy_venom_result_rel H tops runtime_bc tx src r ==>
  deploy_venom_result_rel H tops runtime_bc tx src r'
Proof
  Cases_on `r` >> simp[] >> rpt strip_tac >> gvs[] >>
  Cases_on `src` >> gvs[deploy_venom_result_rel_def] >>
  rename1 `INL pair` >> PairCases_on `pair` >>
  gvs[deploy_venom_result_rel_def]
QED

Theorem gas_origin_path_raw_fmp[local]:
  EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
    inst.inst_opcode <> DALLOCA) (fn_insts fn)) ctx.ctx_functions /\
  EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
    (fn_insts fn) /\
  gas_origin_path memory explicit ctx fn s marks r ==>
  ?r'. raw_fmp_result_rel p i e r r' /\
    gas_origin_path memory explicit ctx fn
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) marks r'
Proof
  strip_tac >> irule gas_origin_path_fmp_update_under_transport >>
  (conj_tac >- (rpt strip_tac >>
    irule gas_origin_edge_fmp_update_under_transport >>
    rpt conj_tac
    >- (rpt strip_tac >>
        pure_rewrite_tac[venom_state_fupdcanon] >>
        irule (iffRL (cj 1 (SRULE [LET_THM] mem_safe_defs_fmp_update_under_execution))) >>
        simp[SRULE [] run_defs_fmp_update, SRULE [] eval_phis_fmp_update,
             SRULE [] setup_callee_fmp_update] >>
        gvs[EVERY_MEM] >> metis_tac[])
    >- (rpt strip_tac >> irule (cj 1 gas_events_fmp_update_under_execution) >>
        simp[SRULE [] run_defs_fmp_update, SRULE [] eval_phis_fmp_update,
             SRULE [] setup_callee_fmp_update] >>
        gvs[EVERY_MEM] >> metis_tac[])
    >- (rpt strip_tac >> irule (cj 1 run_defs_fmp_update) >>
        gvs[EVERY_MEM] >> metis_tac[])
    >- simp[eval_phis_fmp_update] >> goal_assum drule)) >> goal_assum drule
QED

Theorem gas_origin_ptr_path_raw_fmp[local]:
  EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
    inst.inst_opcode <> DALLOCA) (fn_insts fn)) ctx.ctx_functions /\
  EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
    (fn_insts fn) /\
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (r,G',tn') ==>
  ?r'. raw_fmp_result_rel p i e r r' /\
    gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>,G,tn)
      marks (r',G',tn')
Proof
  strip_tac >> irule gas_origin_ptr_path_fmp_update_under_transport >>
  (conj_tac >- (rpt strip_tac >>
    irule gas_origin_ptr_edge_fmp_update_under_transport >>
    rpt conj_tac
    >- (rpt strip_tac >> pure_rewrite_tac[venom_state_fupdcanon] >>
        irule (iffRL (cj 1 (SRULE [LET_THM] ptr_safe_blocks_fmp_update_under_execution))) >>
        simp[SRULE [] run_defs_fmp_update, SRULE [] eval_phis_fmp_update,
             SRULE [] setup_callee_fmp_update, step_inst_non_invoke,
             SRULE [] step_inst_base_fmp_update] >>
        gvs[EVERY_MEM] >> metis_tac[])
    >- (rpt strip_tac >> pure_rewrite_tac[venom_state_fupdcanon] >>
        irule (cj 1 (SRULE [LET_THM] ghost_defs_fmp_update_under_execution)) >>
        simp[SRULE [] run_defs_fmp_update, SRULE [] eval_phis_fmp_update,
             SRULE [] setup_callee_fmp_update, step_inst_non_invoke,
             SRULE [] step_inst_base_fmp_update] >>
        gvs[EVERY_MEM] >> metis_tac[])
    >- (rpt strip_tac >> pure_rewrite_tac[venom_state_fupdcanon] >>
        irule (iffRL (cj 1 (SRULE [LET_THM] mem_safe_defs_fmp_update_under_execution))) >>
        simp[SRULE [] run_defs_fmp_update, SRULE [] eval_phis_fmp_update,
             SRULE [] setup_callee_fmp_update] >>
        gvs[EVERY_MEM] >> metis_tac[])
    >- (rpt strip_tac >> irule (cj 1 gas_events_fmp_update_under_execution) >>
        simp[SRULE [] run_defs_fmp_update, SRULE [] eval_phis_fmp_update,
             SRULE [] setup_callee_fmp_update] >>
        gvs[EVERY_MEM] >> metis_tac[])
    >- (rpt strip_tac >> irule (cj 1 run_defs_fmp_update) >>
        gvs[EVERY_MEM] >> metis_tac[])
    >- simp[eval_phis_fmp_update] >> goal_assum drule)) >> goal_assum drule
QED

Theorem gas_origin_ptr_focus_raw_fmp[local]:
  EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
    inst.inst_opcode <> DALLOCA) (fn_insts fn)) ctx.ctx_functions /\
  MEM fn ctx.ctx_functions /\
  gas_origin_ptr_focus (D,lo,explicit,ctx,fn,PG) (s,G,tn)
    marks (leaf,leaf_pg,leaf_g,leaf_tn,endpoint) ==>
  ?finish'. gas_origin_ptr_focus (D,lo,explicit,ctx,fn,PG)
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>,G,tn)
    marks (leaf,leaf_pg,leaf_g,leaf_tn,finish')
Proof
  strip_tac >>
  `~ctx_has_dalloca ctx` by
    (gvs[ctx_has_dalloca_def, EXISTS_MEM, EVERY_MEM] >> metis_tac[]) >>
  irule gas_origin_ptr_focus_fmp_update_under_transport >>
  rpt conj_tac
  >- (rpt strip_tac >>
      gvs[ptr_inst_ok_def, allocas_from_def,
        SRULE [] access_ok_fmp_fields, SRULE [] taint_ok_fmp_fields] >> metis_tac[])
  >- (rpt strip_tac >> irule gas_origin_ptr_path_raw_fmp >>
      simp[] >> qpat_x_assum `EVERY _ ctx.ctx_functions` mp_tac >>
      simp[EVERY_MEM] >> metis_tac[])
  >- (rpt strip_tac >> irule gas_invoke_entry_fmp_update_under_transport >>
      simp[SRULE [] eval_phis_fmp_update, SRULE [] setup_callee_fmp_update,
           SRULE [] eval_operands_fmp_fields])
  >- simp[] >> metis_tac[]
QED

Theorem ptr_safe_blocks_raw_fmp[local]:
  EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
    inst.inst_opcode <> DALLOCA) (fn_insts fn)) ctx.ctx_functions /\
  EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
    (fn_insts fn) /\ ptr_safe_blocks D lo fuel ctx fn PG G tn s ==>
  ptr_safe_blocks D lo fuel ctx fn PG G tn
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
Proof
  strip_tac >> pure_rewrite_tac[venom_state_fupdcanon] >>
  irule (iffRL (cj 3 (SRULE [LET_THM] ptr_safe_blocks_fmp_update_under_execution))) >>
  simp[SRULE [] run_defs_fmp_update, SRULE [] eval_phis_fmp_update,
       SRULE [] setup_callee_fmp_update, step_inst_non_invoke,
       SRULE [] step_inst_base_fmp_update]
QED

Theorem create_size_exit_ok_raw_fmp[local]:
  raw_fmp_result_rel p i e r r' /\ create_size_exit_ok ctx src r ==>
  create_size_exit_ok ctx src r'
Proof
  Cases_on `r` >> simp[] >> rpt strip_tac >>
  gvs[create_size_exit_ok_def, oversized_create_abort_def] >> metis_tac[]
QED

Theorem deploy_certificate_raw_fmp_transport:
  o1_source_unit_ok unit /\ ~ctx_has_dalloca unit.cu_context /\
  deploy_unit_execution_correct_with shadow_ctx marks tops runtime_bc am tx unit s ==>
  deploy_unit_execution_correct_with shadow_ctx marks tops runtime_bc am tx unit
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
Proof
  strip_tac >>
  `EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
      inst.inst_opcode <> DALLOCA) (fn_insts fn)) unit.cu_context.ctx_functions` by
    (gvs[o1_source_unit_ok_def, ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >>
     metis_tac[]) >>
  gvs[deploy_unit_execution_correct_with_def] >>
  qexists_tac `shadow_func` >> simp[]
  >- (disj1_tac >> qexistsl_tac [`H`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`] >>
      drule_all gas_origin_ptr_focus_raw_fmp >>
      disch_then (assume_tac o SRULE []) >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      simp[] >> qexistsl_tac [`H`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`] >>
      drule_all gas_origin_ptr_focus_raw_fmp >>
      disch_then (assume_tac o SRULE []) >> metis_tac[]) >>
  disj2_tac >> disj2_tac >>
  `EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
      (fn_insts func)` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all gas_origin_path_raw_fmp >>
  disch_then (qspecl_then [`p`, `i`, `e`]
    (qx_choose_then `r2` strip_assume_tac)) >> gvs[] >>
  qexists_tac `r2` >> simp[] >>
  (conj_tac >- metis_tac[raw_fmp_result_rel_exit]) >>
  (conj_tac >- metis_tac[create_size_exit_ok_raw_fmp]) >>
  gen_tac >> strip_tac >>
  (conj_tac >- metis_tac[deploy_venom_result_rel_raw_fmp_transport]) >>
  gen_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` drule >> strip_tac >>
  qpat_x_assum `!fuel. ptr_safe_blocks _ _ _ _ _ _ _ _ _`
    (qspec_then `fuel` assume_tac) >>
  drule_all ptr_safe_blocks_raw_fmp >>
  disch_then (assume_tac o SRULE []) >> metis_tac[]
QED
