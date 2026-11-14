Theory deploySymSrcGenerate
Ancestors
  deploySymSrcHistory runtimeSymSrcModuleBodies runtimeSymSrcInternalFunction
  runtimeSymSrcModuleArgPreservation runtimeSymSrcEmission runtimeSymSrcInterfaces
  runtimeSymSrcModuleDispatch
  moduleLowering compileEnv loweringShapeDefs emitHelper venomInst stackPlanTypes list

Theorem deploy_sym_constructor_setup[local]:
  !ce args size len pay s guard_u st_guard imm st_alloc ce_args st_args.
  runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
  (!ce args off size s ce' s'. runtime_sym_env ce /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_register_constructor_args ce args off size s = (ce',s') ==>
    runtime_sym_env ce' /\ EVERY runtime_sym_inst (state_insts s')) /\
  (if ~pay then
     comp_bind (emit_op CALLVALUE []) (\cv.
       comp_bind (emit_op ISZERO [cv]) (\no_val. emit_void ASSERT [no_val]))
   else comp_return ()) s = (guard_u,st_guard) /\
  (if len > 0 then
     comp_bind (compile_fixed_region_with_id len)
       (\alloc. comp_return ((SND alloc).buf_operand))
   else comp_return (Lit 0w)) st_guard = (imm,st_alloc) /\
  compile_register_constructor_args
    (ce with ce_imm_alloca := if len > 0 then SOME imm else NONE)
    args 0 size st_alloc = (ce_args,st_args) ==>
  runtime_sym_env ce_args /\ EVERY runtime_sym_inst (state_insts st_args) /\
  ~is_label_operand imm
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY runtime_sym_inst (state_insts st_guard)` by
    (qpat_x_assum `(if ~pay then _ else _) s = _` mp_tac >>
     Cases_on `pay` >>
     simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
          emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[] >>
     gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
         runtime_sym_inst_def, mk_inst_def]) >>
  `EVERY runtime_sym_inst (state_insts st_alloc) /\ ~is_label_operand imm` by
    (qpat_x_assum `(if len > 0 then _ else _) st_guard = _` mp_tac >>
     Cases_on `len > 0` >> simp[comp_bind_def, comp_return_def] >>
     strip_tac >> gvs[is_label_operand_def] >>
     pairarg_tac >> gvs[] >>
     drule_all runtime_sym_fixed_region_with_id >> simp[]) >>
  `runtime_sym_env (ce with ce_imm_alloca := if len > 0 then SOME imm else NONE)` by
    (qpat_x_assum `runtime_sym_env ce` mp_tac >>
     simp[runtime_sym_env_def] >> Cases_on `len > 0` >> simp[] >> metis_tac[]) >>
  `runtime_sym_env ce_args /\ EVERY runtime_sym_inst (state_insts st_args)` by
    (first_x_assum (drule_at (Pat `compile_register_constructor_args _ _ _ _ _ = _`)) >>
     disch_then drule >> disch_then drule >> simp[]) >> simp[]
QED

Theorem deploy_sym_constructor_body[local]:
  !cfg nr key trans ce_args tops bindings body st_args lock_u st_lock
    exit_lbl st_fresh body_u st_body.
  runtime_sym_env ce_args /\ supported_stmts tops bindings body /\
  ~supported_stmts_expr_exists is_self_code body /\
  (!ce'. runtime_sym_stmts_contract tops bindings compile_stmts ce' NoLoop NoneT body) /\
  EVERY runtime_sym_inst (state_insts st_args) /\
  (if nr then (\(a,b,c,view). compile_nonreentrant_lock key trans view) cfg
   else comp_return ()) st_args = (lock_u,st_lock) /\
  fresh_label "ctor_exit" st_lock = (exit_lbl,st_fresh) /\
  compile_stmts (ce_args with ce_ctor_exit_label := SOME exit_lbl)
    NoLoop NoneT body st_fresh = (body_u,st_body) ==>
  runtime_sym_label exit_lbl /\ EVERY runtime_sym_inst (state_insts st_body)
Proof
  rpt gen_tac >> PairCases_on `cfg` >> strip_tac >>
  `EVERY runtime_sym_inst (state_insts st_lock)` by
    (Cases_on `nr` >> gvs[comp_return_def] >>
     metis_tac[runtime_sym_nonreentrant_lock]) >>
  drule runtime_sym_fresh_label >> strip_tac >>
  `runtime_sym_env (ce_args with ce_ctor_exit_label := SOME exit_lbl)` by
    (qpat_x_assum `runtime_sym_env ce_args` mp_tac >>
     simp[runtime_sym_env_def] >> metis_tac[]) >>
  simp[] >>
  qpat_x_assum `!ce'. runtime_sym_stmts_contract _ _ _ ce' _ _ _` mp_tac >>
  simp[runtime_sym_stmts_contract_def, runtime_sym_loop_def] >>
  disch_then (qspec_then `ce_args with ce_ctor_exit_label := SOME exit_lbl` mp_tac) >>
  simp[] >> disch_then (qspecl_then [`st_fresh`,`st_body`] mp_tac) >>
  Cases_on `body_u` >> simp[]
QED

Theorem deploy_sym_constructor_finish[local]:
  !cfg nr key trans exit_lbl imm rt len ints st_body jump_u st_jump
    block_u st_exit unlock_u st_unlock epi_u st_epi s'.
  runtime_sym_label exit_lbl /\ ~is_label_operand imm /\
  EVERY runtime_sym_inst (state_insts st_body) /\
  (!s s'. EVERY deploy_sym_inst (state_insts s) /\
    compile_internal_fn_bodies ints s = ((),s') ==>
    EVERY deploy_sym_inst (state_insts s')) /\
  (if block_is_terminated st_body then comp_return ()
   else emit_inst JMP [Label exit_lbl] []) st_body = (jump_u,st_jump) /\
  new_block exit_lbl st_jump = (block_u,st_exit) /\
  (if nr then (\(a,b,c,view). compile_nonreentrant_unlock key trans view) cfg
   else comp_return ()) st_exit = (unlock_u,st_unlock) /\
  compile_constructor_epilogue rt len imm st_unlock = (epi_u,st_epi) /\
  compile_internal_fn_bodies ints st_epi = ((),s') ==>
  EVERY deploy_sym_inst (state_insts s')
Proof
  rpt gen_tac >> PairCases_on `cfg` >> strip_tac >>
  `EVERY runtime_sym_inst (state_insts st_jump)` by
    (qpat_x_assum `(if block_is_terminated _ then _ else _) _ = _` mp_tac >>
     Cases_on `block_is_terminated st_body` >> simp[comp_return_def] >>
     metis_tac[runtime_sym_jump]) >>
  `EVERY runtime_sym_inst (state_insts st_exit)` by
    (drule_at (Pat `new_block _ _ = _`) runtime_sym_new_block_result >> simp[]) >>
  `EVERY runtime_sym_inst (state_insts st_unlock)` by
    (Cases_on `nr` >> gvs[comp_return_def] >>
     metis_tac[runtime_sym_nonreentrant_unlock]) >>
  `EVERY deploy_sym_inst (state_insts st_unlock)` by
    metis_tac[EVERY_MEM, runtime_sym_inst_deploy] >>
  drule_all deploy_sym_constructor_epilogue >>
  disch_then (qspecl_then [`rt`,`len`] mp_tac) >> simp[] >> strip_tac >>
  first_x_assum (drule_at (Pat `compile_internal_fn_bodies _ _ = _`)) >> simp[]
QED

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
  rename1 `(if ~pay then _ else _) s = (guard_u,st_guard)` >>
  qpat_x_assum `(\(_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `(if len > 0 then _ else _) st_guard = (imm,st_alloc)` >>
  qpat_x_assum `(\(_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_register_constructor_args _ _ _ _ st_alloc = (ce_args,st_args)` >>
  drule_all deploy_sym_constructor_setup >> strip_tac >>
  qpat_x_assum `(\(_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `(if nr then _ else _) st_args = (lock_u,st_lock)` >>
  qpat_x_assum `(\(_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `fresh_label "ctor_exit" st_lock = (exit_lbl,st_fresh)` >>
  qpat_x_assum `(\(_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[comp_get_def] >> strip_tac >>
  rename1 `compile_stmts _ _ _ _ st_fresh = (body_u,st_body)` >>
  drule_all deploy_sym_constructor_body >> strip_tac >>
  qpat_x_assum `(\(_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `(if block_is_terminated st_body then _ else _) st_body = (jump_u,st_jump)` >>
  qpat_x_assum `(\(_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `new_block exit_lbl st_jump = (block_u,st_exit)` >>
  qpat_x_assum `(\(_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `(if nr then _ else _) st_exit = (unlock_u,st_unlock)` >>
  qpat_x_assum `(\(_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_constructor_epilogue rt len imm st_unlock = (epi_u,st_epi)` >>
  drule_all deploy_sym_constructor_finish >> simp[]
QED
