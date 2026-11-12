Theory extRetStaticReservedPtr
Ancestors
  extRetStaticStmtPtr exprOperandVar extRetCopyInputsPtr extRetNormalEvidencePtr
  extRetSomeComposePtr bodyPtrDefs typedCopyPtr loweringPosts stmtSimReturn
  exprLowering exprLoweringProps gasSummaryComposePtr

Theorem external_return_static_copy_stmt_frag_ptr_reserved:
  cenv.ce_return_pc = NONE /\ ~is_word_type ty /\
  ~is_word_type (expr_type e) /\ ~cenv.ce_raw_return /\
  cenv.ce_nonreentrant = (F,nkey,ut,iv) /\ cenv.ce_ret_enc_info = AbiCopy m /\
  (is_bytestring_type ty /\ is_bytestring_type (lowered_value_type cenv e) \/
   lowered_value_type cenv e = ty) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_dynamic (vyper_to_abi_type (get_tenv cx) (expr_type e)) /\
  m = type_memory_size tv /\ m <= cenv.ce_max_return_size /\
  cenv.ce_max_return_size < dimword (:256) /\
  expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
  call_evaluation_safe cx (int_calls_expr e) /\
  post_value_type cenv e = expr_type e /\
  expr_sim_ptr d ctx PG func cenv cx ty e es ==>
  stmt_frag_ptr d ctx PG func cx lctx (\v es gt r. T) cenv
    (stmt_env cenv lctx ty (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >> rw[stmt_frag_ptr_def] >>
  drule external_return_static_copy_stmt_parts >> simp[] >>
  disch_then drule_all >> strip_tac >>
  drule_at (Pat `lower_value _ _ _ _ _ = _`) compile_lower_value_var >>
  simp[] >> disch_then assume_tac >>
  drule return_forced_admissible >> strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_ptr_def] >>
  disch_then (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  dxrule gas_outcome_ptr_normal_evidence >> strip_tac >>
  drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)
    external_return_some_outcome_ptr >>
  disch_then irule >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all expr_post_ptr_return_inputs >> strip_tac >>
  drule_all external_return_forced_value_typed >> strip_tac >>
  `expr_val_at cenv cx (expr_type e) sa sm ee v op t` by gvs[expr_post_def] >>
  drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)
    compile_external_return_static_copy_gas_path_ptr >>
  simp[] >> disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then drule_all >> simp[]
QED
