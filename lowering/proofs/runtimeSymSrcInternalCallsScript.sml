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

Theorem runtime_sym_widen_operands[local]:
  EVERY (\op. ~is_label_operand op) ops ==>
  EVERY (\op. ~is_label_operand op \/ ?l. op = Label l /\ runtime_sym_label l) ops
Proof
  simp[EVERY_MEM] >> metis_tac[]
QED

fun intcall_stage_tac equation =
  qpat_assum equation (fn step =>
    qpat_assum `!cfn ce es flags tys s ops s'. _`
      (fn stage => mp_tac (MATCH_MP stage step))) >>
  (impl_tac >- simp[]) >> strip_tac;

val stages =
  intcall_stage_tac `compile_stage_intcall_args _ ce _ _ _ _ = _` >>
  intcall_stage_tac `compile_stage_intcall_args _ (cenv_without_defaults _ _) _ _ _ _ = _`;

Theorem runtime_sym_call_internal:
  (!sz s buf s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer sz s = (buf,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand buf.buf_operand) /\
  (!cfn ce es flags tys s ops s'.
    compile_stage_intcall_args cfn ce es flags tys s = (ops,s') ==>
    runtime_sym_env tops ce /\ EVERY (supported_pure_expr tops) es /\
    ~supported_exprs_exists is_self_code es /\
    (!e t. MEM e es ==> runtime_sym_expr_contract tops cfn ce t e) /\
    EVERY runtime_sym_inst (state_insts s) ==>
    EVERY runtime_sym_inst (state_insts s') /\
    EVERY (\op. ~is_label_operand op) ops) /\
  (!ops buf off s u s'. EVERY (\op. ~is_label_operand op) ops /\
    ~is_label_operand buf /\ EVERY runtime_sym_inst (state_insts s) /\
    store_multi_results buf ops off s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !cfn ce rt ty fid es default s v s'.
    (!e t. MEM e es \/ default = SOME e ==>
      runtime_sym_expr_contract tops cfn ce t e) /\
    (!e t. MEM e (omitted_defaults ce (nsid_to_string fid) (LENGTH es)) ==>
      runtime_sym_expr_contract tops cfn
        (cenv_without_defaults ce (nsid_to_string fid)) t e) /\
    runtime_sym_env tops ce /\ supported_expr tops (Call rt (IntCall fid) es default) /\
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
  drule runtime_sym_env_defaults >>
  disch_then (strip_assume_tac o MATCH_MP
    (Q.INST [`name` |-> `nsid_to_string fid`, `nargs` |-> `LENGTH (es : expr list)`]
      runtime_sym_omitted_defaults)) >>
  qpat_x_assum `compile_call _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_call_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  `!e t. MEM e es ==> runtime_sym_expr_contract tops cfn ce t e` by metis_tac[] >>
  Cases_on `returns_count > 0` >> gvs[]
  >- (ntac 5 (pairarg_tac >> gvs[]) >>
      qpat_assum `!sz s buf s'. _` drule_all >> strip_tac >>
      stages >>
      drule_at (Pat `emit_multi_op _ _ _ _ = _`) runtime_sym_emit_multi_op >>
      simp[runtime_sym_internal_label, EVERY_APPEND, runtime_sym_widen_operands] >>
      strip_tac >>
      pairarg_tac >> gvs[] >>
      first_assum (drule_at (Pat `store_multi_results _ _ _ _ = _`)) >>
      simp[runtime_sym_value_def, base_ptr_def]) >>
  Cases_on `return_buf_size > 0` >> gvs[]
  >- (rpt (pairarg_tac >> gvs[]) >>
      qpat_assum `!sz s buf s'. _` drule_all >> strip_tac >>
      stages >>
      drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_invoke_void >>
      simp[runtime_sym_internal_label, EVERY_APPEND, runtime_sym_value_def, base_ptr_def]) >>
  rpt (pairarg_tac >> gvs[]) >> stages >>
  drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_invoke_void >>
  simp[runtime_sym_internal_label, EVERY_APPEND, runtime_sym_value_def, is_label_operand_def]
QED
