(* Raw deploy instruction checks shared by both unit lowerers. *)
Theory deployLabelRunners
Ancestors
  runtimeLabelInvariant runtimeLabelGenerators runtimeLabelPrimitives
  runtimeLabelValues runtimeLabelABI runtimeLabelStmt runtimeLabelExpr
  compileVyper vyperCompiler moduleLowering compileEnv emitHelper
  loweringPackageInsts loweringShapeDefs venomInst list finite_map

Theorem deploy_body_args_checks[local]:
  !args ce offset data_size. rb_env_ok_for checks ce ==>
    rb_step_for checks (rb_env_ok_for checks)
      (compile_register_constructor_args ce args offset data_size)
Proof
  Induct >> simp[compile_register_constructor_args_def, rb_step_return_for] >>
  PairCases >> rpt gen_tac >> strip_tac >>
  rewrite_tac[compile_register_constructor_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  rename1 `_ = SOME loc` >> Cases_on `var_location_memory_size loc` >> simp[] >>
  irule rb_bind_alloc_buffer_for >> BETA_TAC >>
  qx_gen_tac `buf` >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  rename1 `PtrVar buf.buf_operand bytes` >>
  `rb_env_ok_for checks (ce with ce_vars updated_by
      (\m. m |+ (h0,PtrVar buf.buf_operand bytes)))` by
    metis_tac[rb_env_bind_local_for, rb_location_ok_for_def] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >>
  simp[rb_compile_decode_args_for]
QED

Theorem deploy_epilogue_checks[local]:
  "runtime_begin" NOTIN FST checks /\ rb_operand_ok_for checks imm ==>
  rb_step_for checks (K T) (compile_constructor_epilogue runtime len imm)
Proof
  strip_tac >> Cases_on `0 < len` >>
  simp_tac std_ss [compile_constructor_epilogue_def, LET_THM] >> simp[]
  >- (irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      rpt (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >>
           conj_tac >- simp[rb_emit_void_for]) >>
      simp[rb_emit_inst_for]) >>
  irule rb_bind_alloc_buffer_for >> BETA_TAC >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >>
  simp[rb_emit_void_for, rb_emit_inst_for]
QED

Theorem simple_deploy_checks[local]:
  "runtime_begin" NOTIN FST checks ==>
  rb_step_for checks (K T) (compile_simple_deploy runtime len)
Proof
  strip_tac >> simp_tac std_ss [compile_simple_deploy_def, LET_THM] >>
  irule rb_bind_alloc_buffer_for >> BETA_TAC >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >>
  simp[rb_emit_void_for, rb_emit_inst_for]
QED

Theorem generate_deploy_checks:
  "runtime_begin" NOTIN FST checks /\
  (has ==> rb_env_ok_for checks ce /\
    EVERY (\(lbl,cenv,params,has_buf,nr,key,trans,view,ctor,imm_len,stmts,ret).
      rb_env_ok_for checks cenv) ints) ==>
  rb_step_for checks (K T)
    (compile_generate_deploy has runtime len args data_size ints ce ctor_body pay nr key trans)
Proof
  reverse (Cases_on `has`) >> simp_tac std_ss [compile_generate_deploy_def, COND_CLAUSES] >>
  simp[] >> strip_tac
  >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >>
      simp[simple_deploy_checks, rb_step_return_for]) >>
  `rb_stmt_contract_for checks` by simp[compile_expr_label_checks, compile_stmts_label_checks] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- (Cases_on `pay` >> simp[rb_step_return_for] >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_void_for]) >>
  irule rb_step_bind_for >> qexists_tac `rb_operand_ok_for checks` >>
  BETA_TAC >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return_for] >>
      irule rb_step_bind_for >>
      qexists_tac `\ib. rb_buffer_ok_for checks (SND ib)` >>
      simp[rb_compile_fixed_region_with_id_for, rb_step_return_for, rb_buffer_ok_for_def]) >>
  qx_gen_tac `imm` >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `rb_env_ok_for checks` >>
  BETA_TAC >> reverse conj_tac
  >- (irule deploy_body_args_checks >> IF_CASES_TAC >> gvs[rb_env_ok_for_def] >> metis_tac[]) >>
  qx_gen_tac `ce'` >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- (Cases_on `nr` >> simp[rb_step_return_for] >>
      Cases_on `ce.ce_nonreentrant` >> rename1 `(enabled,rest)` >> PairCases_on `rest` >>
      simp[rb_compile_nonreentrant_lock_for]) >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> qx_gen_tac `exit` >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- (fs[rb_stmt_contract_for_def] >> first_x_assum irule >>
      simp[rb_loop_ok_for_def, rb_env_ok_for_def] >> gvs[rb_env_ok_for_def] >> metis_tac[]) >>
  irule rb_step_bind_for >> qexists_tac `K T` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_step_for_def, comp_get_def] >>
  gen_tac >> simp[] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_emit_inst_for, rb_step_return_for]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- simp[rb_new_block_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- (Cases_on `nr` >> simp[rb_step_return_for] >>
      Cases_on `ce.ce_nonreentrant` >> rename1 `(enabled,rest)` >> PairCases_on `rest` >>
      simp[rb_compile_nonreentrant_unlock_for]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- simp[deploy_epilogue_checks] >>
  simp[rb_compile_internal_fn_bodies_for]
QED

Theorem run_deploy_lowering_checks:
  rb_step_for checks (K T)
    (compile_generate_deploy has (LENGTH bytes) len args data_size ints ce ctor_body pay nr key trans) /\
  run_deploy_lowering has rp bytes len args data_size ints ce ctor_body pay nr key trans entry = SOME unit /\
  MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
  source_inst_ok checks inst
Proof
  simp[run_deploy_lowering_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[AllCaseEqs(), install_immutable_reservation_def] >>
  `rb_state_ok_for checks st1` by
    (qpat_x_assum `rb_step_for _ _ _` mp_tac >>
     simp[rb_step_for_def] >>
     disch_then (qspec_then `initial_compile_state entry` mp_tac) >>
     simp[rb_state_ok_for_def, every_state_insts_initial]) >>
  fs[rb_state_ok_for_def] >>
  drule_all extract_context_with_internals_every >> simp[EVERY_MEM] >> metis_tac[]
QED
