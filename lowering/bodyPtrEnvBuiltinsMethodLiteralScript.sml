(* Folded MethodId words execute no target instruction. *)
Theory bodyPtrEnvBuiltinsMethodLiteral
Ancestors
  exprSimHash exprLowering exprLoweringProps emitHelper compileEnv
  vyperInterpreter vyperValue vyperContext vyperAST valueEncoding vyperState
  exprSimLiteralBuffer bodyPtrDefs bodyPtrEnvBuiltinsScalar
  bodyPtrEnvBuiltinsEdges bodyPtrEnvBuiltinsBoundary exprSimPrecompiles
  gasSummary fragGasPathPtr stmtFragPtr loweringPosts
  venomState ptrDiscipline words list vyperTypeBytesCrypto
  exprPtrUnwrap bodyPtrPreds exprSimProps exprSimWordArgs venomInst
  vyperTypeSystem

Theorem method_literal_source:
  method_id_literal (Literal la l) = SOME bs ==>
  bind (eval_expr cx (Builtin ann MethodId [Literal la l])) (read_result cx) es =
    (INL (BytesV (TAKE 4 (Keccak_256_w64 bs))), es)
Proof
  strip_tac >>
  Cases_on `eval_expr cx (Builtin ann MethodId [Literal la l]) es` >>
  drule_all eval_expr_method_id_literal >> strip_tac >>
  gvs[bind_def, read_result_def, return_def]
QED

Theorem method_literal_word_lower:
  method_id_literal (Literal la l) = SOME bs ==>
  lower_value compile_expr cenv ty
    (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) sa =
    (Lit (typed_val_to_w256 (BaseTV (BytesT (Fixed 4)))
      (BytesV (TAKE 4 (Keccak_256_w64 bs)))), sa)
Proof
  strip_tac >> drule compile_expr_method_id_literal >> strip_tac >>
  simp[lower_value_def, compile_literal_vv_def, comp_bind_def,
       unwrap_value_def, comp_return_def]
QED

Theorem method_literal_word_post:
  method_id_literal (Literal la l) = SOME bs /\
  lower_value compile_expr cenv ty
    (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) sa = (op,sb) /\
  stmt_state_rel ctx fn cenv cx es s ==>
  expr_post ctx fn cenv cx
    (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) es sa sb s
    (es with gas_obs := []) (BytesV (TAKE 4 (Keccak_256_w64 bs))) op s
Proof
  strip_tac >> drule method_literal_word_lower >>
  disch_then (qspecl_then [`ty`, `sa`, `cenv`] assume_tac) >> gvs[] >>
  irule expr_post_typed_stack_intro >>
  simp[expr_type_def, is_word_type_def, evaluate_type_def, eval_operand_def,
       stmt_state_rel_gas_obs, wb_frame_refl]
QED

Theorem method_literal_word_sim_ptr:
  method_id_literal (Literal la l) = SOME bs ==>
  expr_sim_ptr d ctx PG fn cenv cx ty
    (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) es
Proof
  strip_tac >> rw[expr_sim_ptr_def] >>
  drule_all method_literal_word_post >> strip_tac >>
  drule method_literal_word_lower >>
  disch_then (qspecl_then [`ty`, `sa`, `cenv`] assume_tac) >> gvs[] >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (BytesV (TAKE 4 (Keccak_256_w64 bs)))`, `es`,
               `G0`, `tn0`, `OK s0`] >>
  simp[gas_explicit_def, method_literal_source, expr_type_def,
       is_word_type_def, ghost_inv_gas_obs, ghost_kept_refl,
       ptr_val_ok_def, op_taint_def, Once gas_path_ptr_cases]
QED

Theorem method_literal_word_vv_sim_ptr:
  method_id_literal (Literal la l) = SOME bs ==>
  expr_vv_sim_ptr d ctx PG fn cenv cx ty
    (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) es
Proof
  strip_tac >> irule expr_vv_sim_ptr_stack >> conj_tac
  >- (gen_tac >> drule compile_expr_method_id_literal >>
      simp[compile_literal_vv_def, comp_return_def]) >>
  conj_tac >- metis_tac[eval_expr_builtin_value] >>
  irule method_literal_word_sim_ptr >> simp[]
QED

Theorem body_method_literal_word_ptr_case:
  IS_SOME (method_id_literal (Literal la l)) ==>
  body_expr_ptr_ok cx
    (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l])
Proof
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >> rw[body_expr_ptr_ok_def] >>
  metis_tac[method_literal_word_sim_ptr, method_literal_word_vv_sim_ptr]
QED
