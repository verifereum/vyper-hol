Theory bodyLiteralForceMemory
Ancestors
  loweringPosts
  bodyMemoryPreds bodyLiteralMemory exprSimMemoryValues exprSimMemDefs exprSimHypsDefs exprSimProps
  exprLowering exprLoweringProps fragExecMem
  vyperAST vyperInterpreter vyperTyping valueEncoding
  vyperTypeSystem compileEnv context vyperState exprSimDefs
  vyperValueOperation venomState vyperValue loweringSlice
  vyperTypeCallGraph

(* Prior successful uncounted proof and private tactic, retained for reference.
val literal_word_mem_tac =
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      compile_literal_vv_def, unwrap_value_def, evaluate_literal_def, expr_type_def] >>
  irule frag_exec_mem_refl >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def, expr_type_def,
       eval_operand_def, typed_val_to_w256_word_value, word_value_def] >>
  simp[val_to_w256_def, is_word_type_def, evaluate_type_def];

Theorem compile_literal_word_body_sim_mem:
  !ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es /\ is_word_type ann ==>
    expr_sim_mem ctx func cenv cx ty (Literal ann l) es
Proof
  rpt gen_tac >> strip_tac >>
  rw[expr_sim_mem_def] >>
  gvs[Once evaluate_def, bind_def, read_result_def, return_def,
      expr_sim_pre_def, well_typed_expr_def] >>
  Cases_on `l` >> gvs[well_typed_literal_def]
  >~ [`BoolL b`] >- (Cases_on `b` >> literal_word_mem_tac)
  >~ [`IntL i`] >- literal_word_mem_tac
  >~ [`DecimalL i`] >- literal_word_mem_tac >>
  Cases_on `ann` >> gvs[well_typed_literal_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[well_typed_literal_def, is_word_type_def]
  >~ [`BytesT bd`] >- (Cases_on `bd` >> gvs[is_word_type_def] >>
      literal_word_mem_tac) >>
  literal_word_mem_tac
QED
*)

Theorem compile_literal_word_body_sim_mem:
  !ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es /\ is_word_type ann ==>
    expr_sim_mem ctx func cenv cx ty (Literal ann l) es
Proof
  rpt gen_tac >> strip_tac >>
  irule expr_sim_mem_word_values >>
  reverse conj_tac >- simp[vyperASTTheory.expr_type_def] >>
  rpt gen_tac >> strip_tac >>
  qexistsl_tac [`[]`, `evaluate_literal l`, `es`, `s0`] >>
  irule body_literal_word_mem_prefix >> metis_tac[]
QED

Theorem body_literal_word_mem_case:
  !cx ann l. is_word_type ann ==> body_expr_mem_ok cx (Literal ann l)
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env (Literal ann l) es` by
    gvs[expr_sim_pre_def, expr_body_pre_def, int_calls_expr_def] >>
  metis_tac[compile_literal_word_body_sim_mem,
            compile_literal_word_body_vv_sim_mem]
QED

