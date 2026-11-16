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
  (!s v s'. runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_expr ce ty e s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  !s u s'. runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_stmt ce lc ty (Return (SOME e)) s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "expr") (mk_asm "abi")) >>
  `!dt st v pc s u s'. runtime_sym_env ce /\
    ~is_label_operand v /\ ~is_label_operand pc /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_internal_return_from_env ce dt st v pc s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')` by
    (mp_tac runtime_sym_internal_return_from_env >>
     (impl_tac >- metis_tac[runtime_sym_store_memory, runtime_sym_nonreentrant_unlock]) >> simp[]) >>
  pop_assum (mk_asm "internal") >> rpt strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, lower_value_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rename1 `compile_expr ce ty e s = (vv,sa)` >>
  `EVERY runtime_sym_inst (state_insts sa) /\ runtime_sym_value vv` by
    (asm "expr" drule_all >> simp[]) >>
  gvs[] >> rename1 `unwrap_value ce vv sa = (v,sb)` >>
  `EVERY runtime_sym_inst (state_insts sb) /\ ~is_label_operand v` by
    metis_tac[runtime_sym_unwrap_value] >>
  Cases_on `ce.ce_return_pc` >>
  TRY (rename1 `ce.ce_return_pc = SOME loc` >> Cases_on `loc`) >> simp[]
  >>~- ([`ce.ce_return_pc = SOME (PtrVar _ _)`],
    rpt strip_tac >>
    `!loc. ce.ce_return_pc = SOME loc ==> runtime_sym_loc loc` by gvs[runtime_sym_env_def] >>
    asm "internal" (drule_at (Pat `compile_internal_return_from_env _ _ _ _ _ _ = _`)) >>
    gvs[runtime_sym_loc_def])
  >>~- ([`ce.ce_return_pc = SOME (MemLoc _ _)`],
    simp[comp_bind_def] >> pairarg_tac >> simp[] >> rpt strip_tac >>
    qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
    simp[is_label_operand_def] >> strip_tac >> asm "internal" drule_all >> simp[]) >>
  suspend "external"
QED

Resume runtime_sym_return_some_raw[external]:
  markerLib.RESUME_TAC >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >>
  qmatch_asmsub_abbrev_tac `if norm then _ else _` >>
  `EVERY runtime_sym_inst (state_insts cs') /\ ~is_label_operand ret_op` by
    (Cases_on `norm` >>
     qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
     simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
     drule_all runtime_sym_alloc_buffer >> strip_tac >>
     drule_all runtime_sym_store_memory_typed >> simp[]) >>
  Cases_on `ce.ce_raw_return` >> Cases_on `FST ce.ce_nonreentrant` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
  TRY (qpat_assum `compile_nonreentrant_unlock _ _ _ _ = _` kall_tac >>
       drule_all runtime_sym_nonreentrant_unlock >> strip_tac) >>
  TRY (qpat_assum `compile_alloc_buffer _ _ = _`
       (mp_then Any mp_tac runtime_sym_alloc_buffer) >>
       simp[] >> strip_tac >> drule_all runtime_sym_store_memory_typed >> strip_tac) >>
  mp_tac runtime_sym_external_return >>
  (impl_tac >- (conj_tac
    >- (rpt strip_tac >> drule_all runtime_sym_nonreentrant_unlock >> simp[]) >>
    conj_tac
    >- (rpt strip_tac >> drule_all runtime_sym_alloc_buffer >> simp[]) >>
    asm "abi" ACCEPT_TAC)) >>
  disch_then (drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)) >> simp[]
QED
Finalise runtime_sym_return_some_raw

Theorem runtime_sym_single_return_raw:
  (!s v s'. runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_expr ce ty e s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  !s u s'. runtime_sym_env ce /\ runtime_sym_loop lc /\
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
  runtime_sym_env ce /\
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
  runtime_sym_env ce /\
  (!ce s ce' s'. runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_register_positional_args ce args 4 s = (ce',s') ==>
    runtime_sym_env ce' /\ EVERY runtime_sym_inst (state_insts s')) /\
  (!ce' s u s'. runtime_sym_env ce' /\ EVERY runtime_sym_inst (state_insts s) /\
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
  simp[] >> rpt strip_tac >> first_x_assum drule_all >> simp[]
QED
