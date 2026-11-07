Theory bodyPtrPopReasonLogBoundary
Ancestors bodyPtrPopCompilerBoundary bodyPtrPopArithmeticBoundary
  bodyPtrPopMaterialization bodyPtrPopAllocationBoundary bodyPtrPopTypedCopyBoundary
  bodyPtrPopMutualBoundary bodyPtrPopCompileDomain bodyPtrPopCopyBoundary bodyPtrPopFiniteProducerBoundary
  stmtLowering context compileEnv exprLowering emitHelper supportedStmts list venomInst

Theorem pop_compile_encode_log_topic_boundary:
  pop_comp_boundary sa /\ compile_encode_log_topic v bs sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `bs` >> simp[compile_encode_log_topic_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
     gvs[comp_return_def]]
QED

Theorem pop_compile_log_topic_ops_boundary:
  !topics sa r sb. pop_comp_boundary sa /\
  compile_log_topic_ops topics sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Induct_on `topics` >> simp[compile_log_topic_ops_def]
  >- (rpt strip_tac >> gvs[comp_return_def]) >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_all pop_compile_encode_log_topic_boundary >> simp[],
     first_x_assum drule_all >> simp[], gvs[comp_return_def]]
QED

Theorem pop_compile_log_store_data_boundary:
  !data off sa r sb. pop_comp_boundary sa /\
  compile_log_store_data ce data buf off sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Induct_on `data` >> simp[compile_log_store_data_def, comp_ignore_bind_def]
  >- (rpt strip_tac >> gvs[comp_return_def]) >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
     (qpat_x_assum `(if guard then _ else _) _ = _` mp_tac >>
      rpt IF_CASES_TAC >> simp[] >> strip_tac >> FIRST_PROVE
        [drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[],
         drule_all pop_compile_store_bytestring_boundary >> simp[]]),
     first_x_assum drule_all >> simp[], gvs[comp_return_def]]
QED

Theorem pop_compile_log_eval_all_boundary:
  !es sa r sb. EVERY (supported_pure_expr tops) es /\ pop_comp_boundary sa /\
  compile_log_eval_all ce es sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Induct_on `es` >> simp[compile_log_eval_all_def]
  >- (rpt strip_tac >> gvs[comp_return_def]) >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [(drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
      disch_then irule >> simp[] >> rpt strip_tac >>
      drule pop_domain_pure >> strip_tac >>
      drule_all (cj 1 pop_compile_mutual_boundary) >> simp[]),
     first_x_assum drule_all >> simp[], gvs[comp_return_def]]
QED

Theorem pop_compile_revert_with_reason_boundary:
  pop_comp_boundary sa /\ compile_revert_with_reason ce vv ty mem_size sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_revert_with_reason_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
     drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
     drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[],
     drule_all pop_compile_alloc_buffer_boundary >> simp[],
     drule_all pop_unwrap_value_boundary >> simp[]]
QED

Theorem pop_compile_reason_message_boundary:
  supported_string_reason tops e /\ pop_comp_boundary sa /\
  compile_reason_message ce e sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Cases_on `e` >> simp[compile_reason_message_def, supported_string_reason_def] >>
  rpt strip_tac >>
  FIRST_PROVE
    [(drule pop_domain_pure >> strip_tac >>
      drule_all (cj 1 pop_compile_mutual_boundary) >> simp[]),
     (Cases_on `t` >> Cases_on `l` >>
      TRY (rename1 `BaseT b` >> Cases_on `b`) >>
      gvs[compile_reason_message_def, supported_string_reason_def] >>
      FIRST_PROVE
        [(drule pop_domain_pure >> strip_tac >>
          drule_all (cj 1 pop_compile_mutual_boundary) >> simp[]),
         (rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
             disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
          FIRST_PROVE [drule_all pop_compile_bytelike_literal_boundary >> simp[],
            (qpat_x_assum `compile_expr _ _ (Literal _ _) _ = _` mp_tac >>
             simp[Once compile_expr_def] >> strip_tac >>
             drule_all pop_compile_literal_vv_boundary >> simp[]),
            gvs[comp_return_def]])])]
QED
