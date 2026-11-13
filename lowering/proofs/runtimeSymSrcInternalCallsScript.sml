Theory runtimeSymSrcInternalCalls
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission runtimeSymSrcInterfaces
  exprLowering context compileEnv emitHelper loweringShapeDefs venomInst
  supportedExprs supportedExprTraverse list stackPlanTypes

Theorem runtime_sym_invoke_void[local]:
  runtime_sym_label label /\ EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) /\
  emit_void INVOKE (Label label :: ops) s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
       emit_def, comp_return_def] >> rpt strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, EVERY_APPEND, runtime_sym_inst_def,
      mk_inst_def, runtime_sym_label_def, EVERY_MEM] >>
  rpt strip_tac >> gvs[] >> metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_call_internal:
  runtime_sym_multi_vvs_clause tops /\
  (!sz s buf s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer sz s = (buf,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand buf.buf_operand) /\
  (!ce vals flags tys s ops s'.
    runtime_sym_env ce /\ EVERY runtime_sym_value vals /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_stage_intcall_args ce vals flags tys s = (ops,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\
    EVERY (\op. ~is_label_operand op) ops) /\
  (!ops buf off s u s'. EVERY (\op. ~is_label_operand op) ops /\
    ~is_label_operand buf /\ EVERY runtime_sym_inst (state_insts s) /\
    store_multi_results buf ops off s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !cfn ce rt ty fid es default s v s'.
    (!e t. MEM e es \/ default = SOME e ==>
      runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env ce /\ supported_expr tops (Call rt (IntCall fid) es default) /\
    ~supported_expr_exists is_self_code (Call rt (IntCall fid) es default) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_call cfn ce rt (ty : type) (IntCall fid) es default s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `EVERY (supported_pure_expr tops) es` by
    (Cases_on `default` >>
     gvs[supported_expr_def, supported_pure_expr_def,
         supported_effect_expr_def, supported_pure_exprs_every]) >>
  `~supported_exprs_exists is_self_code es` by
    gvs[supported_expr_exists_def] >>
  qpat_x_assum `compile_call _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_call_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  `!e t. MEM e es ==> runtime_sym_expr_contract tops cfn ce t e` by metis_tac[] >>
  qpat_x_assum `runtime_sym_multi_vvs_clause tops` mp_tac >>
  pure_rewrite_tac[runtime_sym_multi_vvs_clause_def] >> disch_then drule_all >>
  strip_tac >>
  Cases_on `returns_count > 0` >> gvs[]
  >- (ntac 5 (pairarg_tac >> gvs[]) >>
      qpat_assum `!sz s buf s'. _` drule_all >> strip_tac >>
      qpat_assum `!ce vals flags tys s ops s'. _` drule_all >> strip_tac >>
      drule_at (Pat `emit_multi_op _ _ _ _ = _`) runtime_sym_emit_multi_op >>
      simp[runtime_sym_internal_label] >>
      (impl_tac >- (gvs[EVERY_MEM] >> metis_tac[])) >> strip_tac >>
      qpat_assum `!ops buf off s s'. _ ==> EVERY runtime_sym_inst (state_insts s')` drule_all >>
      simp[runtime_sym_value_def, base_ptr_def]) >>
  Cases_on `return_buf_size > 0` >> gvs[]
  >- (ntac 4 (pairarg_tac >> gvs[]) >>
      qpat_assum `!sz s buf s'. _` drule_all >> strip_tac >>
      qpat_assum `!ce vals flags tys s ops s'. _` drule_all >> strip_tac >>
      drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_invoke_void >>
      simp[runtime_sym_internal_label, runtime_sym_value_def, base_ptr_def]) >>
  ntac 2 (pairarg_tac >> gvs[]) >>
  qpat_assum `!ce vals flags tys s ops s'. _` drule_all >> strip_tac >>
  drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_invoke_void >>
  simp[runtime_sym_internal_label, runtime_sym_value_def, is_label_operand_def]
QED
