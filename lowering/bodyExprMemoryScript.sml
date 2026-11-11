(* Actual expression producers for the memory body induction. *)
Theory bodyExprMemory
Ancestors
  bodyMemoryDefs exprSimDefs exprSimHypsDefs exprSimProps bodySim
  exprSimMemoryValues exprSimMemoryStack fragGasPathMem fragExecMem loweringSlice
  exprSimMemDefs loweringPosts gasOutcome gasSummary fragGasMode exprLoweringProps
  exprLowering context compileEnv vyperInterpreter vyperValue vyperState
  vyperValueOperation valueEncoding valueEncodingProofs venomState venomExecSemantics

Theorem body_bool_literal_mem:
  !tops ctx func cenv cx env ty b es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Literal (BaseT BoolT) (BoolL b)) es ==>
    expr_sim_mem ctx func cenv cx ty (Literal (BaseT BoolT) (BoolL b)) es /\
    expr_vv_sim_mem ctx func cenv cx ty (Literal (BaseT BoolT) (BoolL b)) es
Proof
  (* Previous fixed-result memory proof (preserved verbatim):
  rpt gen_tac >> strip_tac >> Cases_on `b` >>
  rw[expr_sim_mem_def, expr_vv_sim_mem_def] >>
  gvs[Once evaluate_def, bind_def, read_result_def, return_def,
      lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      compile_literal_vv_def, unwrap_value_def, evaluate_literal_def] >>
  irule frag_exec_mem_refl >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vv_post_def, vv_holds_def, vv_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def,
       typed_val_to_w256_word_value, word_value_def, val_to_w256_def,
       locals_kept_mem, is_word_type_def, read_result_def, return_def]
  *)
  rpt gen_tac >> strip_tac >> Cases_on `b` >>
  rw[expr_sim_mem_def, expr_vv_sim_mem_def] >>
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      compile_literal_vv_def, unwrap_value_def] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qrefinel [`_`, `es`, `OK s0`] >>
  simp[gas_marked_exec_def, gas_marked_path_def,
       Once evaluate_def, bind_def, read_result_def, return_def,
       evaluate_literal_def] >>
  (conj_tac >- metis_tac[gas_path_mem_rules]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vv_post_def, vv_holds_def, vv_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def,
       typed_val_to_w256_word_value, word_value_def, val_to_w256_def,
       locals_kept_mem, is_word_type_def, read_result_def, return_def,
       expr_store_bound_word, vv_store_bound_stack_word]
QED

