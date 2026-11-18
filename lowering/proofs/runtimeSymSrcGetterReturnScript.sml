Theory runtimeSymSrcGetterReturn
Ancestors
  runtimeSymSrcStatementReturns runtimeSymSrcModuleBodies
  runtimeSymSrcContextTyped runtimeSymSrcContextComplete runtimeSymSrcContext
  runtimeSymSrcOpenValues runtimeSymSrcLiteralEnv runtimeSymSrcInterfaces
  runtimeSymSrcEmission
  stmtLowering exprLowering moduleLowering compileEnv context venomInst list
  stackPlanTypes emitHelper loweringShapeDefs

(* Raw safety deliberately has no supported-syntax premise. *)
Theorem runtime_sym_return_some_raw[local]:
  (!s v s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_expr ce ty e s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  !s u s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_stmt ce lc ty (Return (SOME e)) s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> match_mp_tac runtime_sym_return_some_step >>
  qexists_tac `tops` >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- metis_tac[runtime_sym_unwrap_value]
  >- (match_mp_tac runtime_sym_internal_return_from_env >>
      metis_tac[runtime_sym_store_memory, runtime_sym_nonreentrant_unlock])
  >- (match_mp_tac runtime_sym_external_return >>
      metis_tac[runtime_sym_nonreentrant_unlock, runtime_sym_alloc_buffer])
  >- metis_tac[runtime_sym_alloc_buffer]
  >- metis_tac[runtime_sym_store_memory_typed]
  >> metis_tac[runtime_sym_nonreentrant_unlock]
QED

Theorem runtime_sym_single_return_raw:
  (!s v s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_expr ce ty e s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  !s u s'. runtime_sym_env tops ce /\ runtime_sym_loop lc /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_stmts ce lc ty [Return (SOME e)] s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> rpt gen_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_get_def] >>
  IF_CASES_TAC >- (simp[comp_return_def] >> metis_tac[]) >>
  simp[declare_stmt_local_def, comp_bind_def, comp_return_def] >>
  simp[comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `compile_stmts _ _ _ [] _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_return_def] >> strip_tac >> gvs[] >>
  mp_tac runtime_sym_return_some_raw >>
  (impl_tac >- (conj_tac
    >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
    first_assum ACCEPT_TAC)) >>
  disch_then drule_all >> simp[]
QED

Theorem runtime_sym_guarded_body_raw:
  runtime_sym_env tops ce /\
  (!s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_stmts ce NoLoop (case ret of SOME ty => ty | NONE => BaseT BoolT)
      stmts s = (u,s') ==> EVERY runtime_sym_inst (state_insts s')) ==>
  !s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_guarded_body ce nr key trans view stmts ret s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> simp[compile_guarded_body_def, comp_ignore_bind_def] >>
  match_mp_tac runtime_sym_bind >> conj_tac
  >- (Cases_on `nr` >> simp[comp_return_def] >>
      metis_tac[runtime_sym_nonreentrant_lock]) >>
  gen_tac >> BETA_TAC >> match_mp_tac runtime_sym_bind >> conj_tac
  >- first_assum ACCEPT_TAC >>
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

Theorem runtime_sym_external_body_raw:
  runtime_sym_env tops ce /\
  (!ce s ce' s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_register_positional_args ce args 4 s = (ce',s') ==>
    runtime_sym_env tops ce' /\ EVERY runtime_sym_inst (state_insts s')) /\
  (!ce' s u s'. runtime_sym_env tops ce' /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_stmts ce' NoLoop (case ret of SOME ty => ty | NONE => BaseT BoolT)
      stmts s = (u,s') ==> EVERY runtime_sym_inst (state_insts s')) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_external_function_body ce args nr key trans view stmts ret s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_external_function_body_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `!ce s ce' s'. _` drule_all >> strip_tac >>
  irule runtime_sym_guarded_body_raw >>
  goal_assum (drule_at (Pat `compile_guarded_body _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> qexists_tac `tops` >> simp[] >> rpt strip_tac >>
  first_x_assum drule_all >> simp[]
QED
