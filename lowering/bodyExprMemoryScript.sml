(* Actual expression producers for the memory body induction. *)
Theory bodyExprMemory
Ancestors
  bodyMemoryDefs exprSimDefs exprSimHypsDefs exprSimProps bodySim bodyLiteralMemory
  vyperTypeCallGraph
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
  rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env (Literal (BaseT BoolT) (BoolL b)) es` by
    gvs[expr_sim_pre_def, expr_body_pre_def, int_calls_expr_def] >>
  `is_word_type (BaseT BoolT)` by simp[is_word_type_def] >>
  reverse conj_tac >- metis_tac[compile_literal_word_body_vv_sim_mem] >>
  irule expr_sim_mem_word_values >>
  reverse conj_tac >- simp[vyperASTTheory.expr_type_def] >>
  rpt gen_tac >> strip_tac >>
  qexistsl_tac [`[]`, `evaluate_literal (BoolL b)`, `es`, `s0`] >> conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def, Once evaluate_def,
           bind_def, read_result_def, return_def] >>
      metis_tac[gas_path_mem_rules]) >>
  rpt strip_tac >> irule body_literal_word_mem_prefix >> metis_tac[]
QED

