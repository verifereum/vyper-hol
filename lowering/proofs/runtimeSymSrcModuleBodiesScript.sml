Theory runtimeSymSrcModuleBodies
Ancestors
  runtimeSymSrcEmission runtimeSymSrcInterfaces moduleLowering
  runtimeSymSrcRuntimePackaging compileEnv context venomInst list emitHelper loweringShapeDefs stackPlanTypes

Theorem runtime_sym_internal_param_decls:
  !params idx s captured next s'.
    EVERY runtime_sym_inst (state_insts s) /\
    compile_internal_param_decls params idx s = ((captured,next),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\
    EVERY (\(n,stack,op). ~is_label_operand op) captured
Proof
  Induct >> simp[compile_internal_param_decls_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_internal_param_decls_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[comp_return_def] >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >> simp[is_label_operand_def] >> strip_tac >>
  PairCases_on `rest_result` >> first_x_assum drule >>
  disch_then drule >> simp[]
QED

Theorem runtime_sym_materialize_internal_params:
  !params ce s ce' s'.
    EVERY (\(n,stack,op). ~is_label_operand op) params /\
    runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
    materialize_internal_params ce params s = (ce',s') ==>
    runtime_sym_env ce' /\ EVERY runtime_sym_inst (state_insts s')
Proof
  Induct >> simp[materialize_internal_params_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  Cases_on `h1` >> simp[materialize_internal_params_def] >>
  strip_tac
  >- (Cases_on `FLOOKUP ce.ce_vars h0` >> gvs[]
      >- metis_tac[] >>
      Cases_on `x` >> gvs[]
      >- (Cases_on `emit_op ALLOCA [Lit (n2w n0)] s` >>
      gvs[comp_bind_def, comp_ignore_bind_def] >>
      Cases_on `emit_void MSTORE [q; h2] r` >> gvs[] >>
      drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >> simp[is_label_operand_def] >> strip_tac >>
      drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[] >> strip_tac >>
      `runtime_sym_env (ce with ce_vars updated_by
         (\vars. vars |+ (h0, PtrVar q n0)))` by
        (irule runtime_sym_env_update >> simp[runtime_sym_loc_def]) >>
      metis_tac[]) >> metis_tac[]) >>
  `runtime_sym_env (ce with ce_vars updated_by
     (\vars. vars |+ (h0, PtrVar h2
       (case FLOOKUP ce.ce_vars h0 of SOME (MemLoc _ sz) => sz | _ => 0))))` by
    (irule runtime_sym_env_update >> simp[runtime_sym_loc_def]) >>
  metis_tac[]
QED

Theorem runtime_sym_nonreentrant_lock:
  EVERY runtime_sym_inst (state_insts s) /\
  compile_nonreentrant_lock key trans view s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `trans` >> Cases_on `view` >>
  simp[compile_nonreentrant_lock_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       emit_def] >> strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
      runtime_sym_inst_def, mk_inst_def]
QED

Theorem runtime_sym_nonreentrant_unlock:
  EVERY runtime_sym_inst (state_insts s) /\
  compile_nonreentrant_unlock key trans view s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `trans` >> Cases_on `view` >>
  simp[compile_nonreentrant_unlock_def, comp_return_def] >> strip_tac >> gvs[] >>
  drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >>
  simp[is_label_operand_def]
QED


Theorem runtime_sym_bind:
  (!s v s'. EVERY runtime_sym_inst (state_insts s) /\ f s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s')) /\
  (!v s w s'. EVERY runtime_sym_inst (state_insts s) /\ g v s = (w,s') ==>
     EVERY runtime_sym_inst (state_insts s')) ==>
  !s w s'. EVERY runtime_sym_inst (state_insts s) /\
    compileEnv$comp_bind f g s = (w,s') ==> EVERY runtime_sym_inst (state_insts s')
Proof
  simp[comp_bind_def] >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  pairarg_tac >> simp[] >> strip_tac >> metis_tac[]
QED

Theorem runtime_sym_guarded_body:
  runtime_sym_env ce /\
  (!ce'. runtime_sym_stmts_contract tops bindings compile_stmts ce' NoLoop
    (case ret of SOME ty => ty | NONE => BaseT BoolT) stmts) /\
  supported_stmts tops bindings stmts /\
  ~supported_stmts_expr_exists is_self_code stmts ==>
  !s u s'. EVERY runtime_sym_inst (state_insts s) /\
  compile_guarded_body ce nr key trans view stmts ret s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> simp[compile_guarded_body_def, comp_ignore_bind_def] >>
  match_mp_tac runtime_sym_bind >> conj_tac
  >- (Cases_on `nr` >> simp[comp_return_def] >>
      metis_tac[runtime_sym_nonreentrant_lock]) >>
  gen_tac >> BETA_TAC >> match_mp_tac runtime_sym_bind >> conj_tac
  >- (gvs[runtime_sym_stmts_contract_def, runtime_sym_loop_def] >> metis_tac[]) >>
  gen_tac >> Cases_on `nr` >> Cases_on `view` >> Cases_on `trans` >>
  Cases_on `ret` >>
  simp[comp_bind_def, comp_get_def, compile_nonreentrant_unlock_def,
       comp_return_def, emit_inst_def, emit_void_def, fresh_id_def, emit_def] >>
  rpt gen_tac >> IF_CASES_TAC >>
  simp[comp_return_def, comp_bind_def, comp_ignore_bind_def,
       emit_inst_def, emit_void_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
      runtime_sym_inst_def, mk_inst_def]
QED

Theorem runtime_sym_fallback_body:
  runtime_sym_env ce /\
  (!ce'. runtime_sym_stmts_contract tops bindings compile_stmts ce' NoLoop
    (case ret of SOME ty => ty | NONE => BaseT BoolT) stmts) /\
  supported_stmts tops bindings stmts /\
  ~supported_stmts_expr_exists is_self_code stmts ==>
  !s u s'. EVERY runtime_sym_inst (state_insts s) /\
  compile_fallback_body ce payable nr key trans view stmts ret s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> simp[compile_fallback_body_def, comp_ignore_bind_def] >>
  match_mp_tac runtime_sym_bind >> conj_tac
  >- (Cases_on `payable` >>
      simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
           emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
      rpt gen_tac >> strip_tac >> gvs[] >>
      gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
          runtime_sym_inst_def, mk_inst_def]) >>
  gen_tac >> BETA_TAC >> match_mp_tac runtime_sym_guarded_body >> metis_tac[]
QED

Theorem runtime_sym_external_function_body:
  runtime_sym_env ce /\
  (!ce s ce' s'. runtime_sym_env ce /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_register_positional_args ce args 4 s = (ce',s') ==>
    runtime_sym_env ce' /\ EVERY runtime_sym_inst (state_insts s')) /\
  (!ce'. runtime_sym_stmts_contract tops bindings compile_stmts ce' NoLoop
    (case ret of SOME ty => ty | NONE => BaseT BoolT) stmts) /\
  supported_stmts tops bindings stmts /\
  ~supported_stmts_expr_exists is_self_code stmts /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_external_function_body ce args nr key trans view stmts ret s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_external_function_body_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum drule >> disch_then drule >>
  disch_then drule >> strip_tac >>
  metis_tac[runtime_sym_guarded_body]
QED

Theorem runtime_sym_common_function_body:
  runtime_sym_env ce /\
  runtime_sym_env (compile_register_kwarg_vars ce kwargs) /\
  (!ce s ce' s'. runtime_sym_env ce /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_register_positional_args ce args 4 s = (ce',s') ==>
    runtime_sym_env ce' /\ EVERY runtime_sym_inst (state_insts s')) /\
  (!ce'. runtime_sym_stmts_contract tops bindings compile_stmts ce' NoLoop
    (case ret of SOME ty => ty | NONE => BaseT BoolT) stmts) /\
  supported_stmts tops bindings stmts /\
  ~supported_stmts_expr_exists is_self_code stmts /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_common_function_body ce args kwargs nr key trans view stmts ret s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_common_function_body_def, GSYM compile_external_function_body_def] >>
  strip_tac >> irule runtime_sym_external_function_body >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
