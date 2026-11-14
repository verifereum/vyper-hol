Theory deploySymSrcGenerate
Ancestors
  deploySymSrcHistory runtimeSymSrcModuleBodies runtimeSymSrcInternalFunction
  runtimeSymSrcModuleArgPreservation runtimeSymSrcEmission runtimeSymSrcInterfaces
  moduleLowering compileEnv loweringShapeDefs emitHelper venomInst stackPlanTypes list

Theorem deploy_sym_generate_deploy_cond:
  !ce tops bindings body has rt len args size ints pay nr key trans s u s'.
  runtime_sym_env ce /\ supported_stmts tops bindings body /\
  ~supported_stmts_expr_exists is_self_code body /\
  (!ce'. runtime_sym_stmts_contract tops bindings compile_stmts ce' NoLoop NoneT body) /\
  (!ce args off size s ce' s'. runtime_sym_env ce /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_register_constructor_args ce args off size s = (ce',s') ==>
    runtime_sym_env ce' /\ EVERY runtime_sym_inst (state_insts s')) /\
  (!s u s'. EVERY deploy_sym_inst (state_insts s) /\
    compile_internal_fn_bodies ints s = (u,s') ==>
    EVERY deploy_sym_inst (state_insts s')) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_generate_deploy has rt len args size ints ce body pay nr key trans s = (u,s') ==>
  EVERY deploy_sym_inst (state_insts s')
Proof
  rpt gen_tac >> reverse (Cases_on `has`)
  >- (simp[compile_generate_deploy_def, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      `EVERY deploy_sym_inst (state_insts s)` by
        metis_tac[EVERY_MEM, runtime_sym_inst_deploy] >>
      drule deploy_sym_simple_deploy >>
      disch_then (qspecl_then [`rt`,`len`] mp_tac) >> simp[]) >>
  simp[Once compile_generate_deploy_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  `EVERY runtime_sym_inst (state_insts cs')` by
    (qpat_x_assum `(if ~pay then _ else _) s = _` mp_tac >>
     Cases_on `pay` >>
     simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
          emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[] >>
     gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
         runtime_sym_inst_def, mk_inst_def]) >>
  qpat_x_assum `(\(_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  `EVERY runtime_sym_inst (state_insts cs'') /\ ~is_label_operand imm_alloca` by
    (qpat_x_assum `(if len > 0 then _ else _) cs' = _` mp_tac >>
     Cases_on `len > 0` >> simp[comp_bind_def, comp_return_def] >>
     strip_tac >> gvs[is_label_operand_def] >>
     pairarg_tac >> gvs[] >>
     drule_all runtime_sym_fixed_region_with_id >> simp[]) >>
  `runtime_sym_env (ce with ce_imm_alloca := if len > 0 then SOME imm_alloca else NONE)` by
    (qpat_x_assum `runtime_sym_env ce` mp_tac >>
     simp[runtime_sym_env_def] >> Cases_on `len > 0` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `(\(_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  `runtime_sym_env cenv' /\ EVERY runtime_sym_inst (state_insts cs'3')` by
    (first_x_assum (drule_at (Pat `compile_register_constructor_args _ _ _ _ _ = _`)) >>
     disch_then drule >> disch_then drule >> simp[]) >>
  qpat_x_assum `(\(_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `(if nr then _ else _) st_reg = (lock_u,st_lock)` >>
  `EVERY runtime_sym_inst (state_insts st_lock)` by
    (qpat_x_assum `(if nr then _ else _) _ = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `f ce.ce_nonreentrant` >>
     Cases_on `ce.ce_nonreentrant` >> rename1 `f (a,rest)` >> PairCases_on `rest` >>
     simp[Abbr `f`] >> Cases_on `nr` >>
     simp[comp_return_def] >> metis_tac[runtime_sym_nonreentrant_lock]) >>
  qpat_x_assum `(\(_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule runtime_sym_fresh_label >> strip_tac >>
  `runtime_sym_env (cenv' with ce_ctor_exit_label := SOME exit_lbl)` by
    (qpat_x_assum `runtime_sym_env cenv'` mp_tac >>
     simp[runtime_sym_env_def] >> metis_tac[]) >>
  qpat_x_assum `(\(_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[comp_get_def] >> strip_tac >>
  rename1 `compile_stmts _ _ _ _ st_fresh = (body_u,st_body)` >>
  `EVERY runtime_sym_inst (state_insts st_body)` by
    (qpat_x_assum `!ce'. runtime_sym_stmts_contract _ _ _ ce' _ _ _` mp_tac >>
     simp[runtime_sym_stmts_contract_def, runtime_sym_loop_def] >>
     disch_then (qspec_then `cenv' with ce_ctor_exit_label := SOME exit_lbl` mp_tac) >>
     simp[] >> disch_then (qspecl_then [`st_fresh`,`st_body`] mp_tac) >>
     Cases_on `body_u` >> simp[]) >>
  qpat_x_assum `(\(_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `(if block_is_terminated st_body then _ else _) st_body = (jump_u,st_jump)` >>
  `EVERY runtime_sym_inst (state_insts st_jump)` by
    (qpat_x_assum `(if block_is_terminated _ then _ else _) _ = _` mp_tac >>
     Cases_on `block_is_terminated st_body` >> simp[comp_return_def] >>
     metis_tac[runtime_sym_jump]) >>
  qpat_x_assum `(\(_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `new_block exit_lbl st_jump = (block_u,st_exit)` >>
  `EVERY runtime_sym_inst (state_insts st_exit)` by
    (qpat_x_assum `new_block _ _ = _` mp_tac >>
     simp[new_block_def] >> strip_tac >> gvs[] >>
     gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND]) >>
  qpat_x_assum `(\(_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `(if nr then _ else _) st_exit = (unlock_u,st_unlock)` >>
  `EVERY runtime_sym_inst (state_insts st_unlock)` by
    (qpat_x_assum `(if nr then _ else _) st_exit = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `f ce.ce_nonreentrant` >>
     Cases_on `ce.ce_nonreentrant` >> rename1 `f (a,rest)` >> PairCases_on `rest` >>
     simp[Abbr `f`] >> Cases_on `nr` >> simp[comp_return_def] >>
     metis_tac[runtime_sym_nonreentrant_unlock]) >>
  qpat_x_assum `(\(_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  `EVERY deploy_sym_inst (state_insts st_unlock)` by
    metis_tac[EVERY_MEM, runtime_sym_inst_deploy] >>
  drule_all deploy_sym_constructor_epilogue >>
  disch_then (qspecl_then [`rt`,`len`] mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum (drule_at (Pat `compile_internal_fn_bodies _ _ = _`)) >>
  simp[]
QED
