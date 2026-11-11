(* The fixed selector fold is a zero-instruction memory prefix. *)
Theory bodyMemBiMethodIdLiteral
Ancestors
  bodyMemoryPreds exprSimHash bodyLiteralMemory exprSimMemoryValues
  exprSimMemoryStack gasNormalPrefix fragGasPathMem
  exprLowering emitHelper compileEnv vyperAST vyperInterpreter vyperState
  vyperValueOperation loweringPosts venomState venomExecSemantics
  gasSummary exprSimProps exprSimDefs fragGasMode exprLoweringProps

Theorem method_id_literal_word_mem_sim:
  !ctx func cenv cx ty la l es.
    IS_SOME (method_id_literal (Literal la l)) ==>
    expr_sim_mem ctx func cenv cx ty
      (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) es
Proof
  rpt gen_tac >> simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  irule expr_sim_mem_word_values >>
  simp[expr_type_def, is_word_type_def] >> rpt gen_tac >> strip_tac >>
  `!st. eval_expr cx
      (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) st =
      (INL (Value (BytesV (TAKE 4 (Keccak_256_w64 x)))), st)` by
    (gen_tac >> Cases_on `eval_expr cx
      (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) st` >>
     drule_all eval_expr_method_id_literal >> simp[]) >>
  drule compile_expr_method_id_literal >> strip_tac >>
  gvs[lower_value_def, comp_bind_def, compile_literal_vv_def,
      unwrap_value_def, comp_return_def] >>
  qexistsl_tac [`[]`, `BytesV (TAKE 4 (Keccak_256_w64 x))`, `es`, `s0`] >>
  simp[gas_value_prefix_def] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[gas_marked_exec_def, gas_marked_path_def, bind_def,
       read_result_def, return_def, expr_post_def, expr_val_rel_def,
       expr_val_at_def, expr_type_def, eval_operand_def,
       is_word_type_def, vyperValueTheory.evaluate_type_def] >>
  conj_tac
  >- simp[lower_value_def, comp_bind_def, compile_literal_vv_def,
          unwrap_value_def, comp_return_def] >>
  irule (cj 1 gas_path_mem_rules) >> simp[]
QED

Theorem body_method_id_literal_word_mem:
  !cx la l. IS_SOME (method_id_literal (Literal la l)) ==>
    body_expr_mem_ok cx
      (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l])
Proof
  rpt gen_tac >> strip_tac >> rw[body_expr_mem_ok_def] >>
  `expr_sim_mem ctx func cenv cx ty
      (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) es` by
    simp[method_id_literal_word_mem_sim] >> simp[] >>
  irule body_expr_vv_sim_mem_stack_word >>
  simp[expr_type_def, is_word_type_def] >> conj_tac
  >- (gvs[optionTheory.IS_SOME_EXISTS] >> gen_tac >>
      drule compile_expr_method_id_literal >>
      disch_then (qspecl_then [`cenv`, `ty`, `BaseT (BytesT (Fixed 4))`, `sa`]
        mp_tac) >>
      simp[compile_literal_vv_def, comp_return_def]) >>
  metis_tac[eval_expr_builtin_value]
QED
