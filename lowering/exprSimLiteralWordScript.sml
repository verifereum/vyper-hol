(* Counted simulation for word literals. *)
Theory exprSimLiteralWord
Ancestors
  exprSimProps gasNormalPrefix gasSummary fragGasMode fragGasPath
  exprSimDefs exprSimStack exprSimValues
  loweringPosts
  list rich_list finite_map pred_set
  fragExec varsExt loweringSlice localPtrsProps venomMemDefs
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperValueOperation vyperContext
  valueEncoding valueEncodingProofs vyperTypeSystem
  venomExecSemantics venomInst venomState
  vyperLookupStorage vyperStorageBackend

Theorem literal_read_all_tails:
  !cx ann l es tail.
    bind (eval_expr cx (Literal ann l)) (read_result cx)
      (es with gas_obs := tail) =
    (INL (evaluate_literal l), es with gas_obs := tail)
Proof
  simp[Once evaluate_def, bind_def, read_result_def, return_def]
QED

val literal_prefix_tac =
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      compile_literal_vv_def, unwrap_value_def, evaluate_literal_def,
      vyperASTTheory.expr_type_def] >>
  conj_tac >- (irule (cj 1 gas_path_rules) >> simp[]) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def,
       typed_val_to_w256_word_value, word_value_def, val_to_w256_def];

Theorem literal_word_prefix[local]:
  !ctx func cenv cx ty ann l es sa sb op s0.
    is_word_type ann /\
    ((?b. l = BoolL b) \/ (?i. l = IntL i) \/ (?i. l = DecimalL i)) /\
    lower_value compile_expr cenv ty (Literal ann l) sa = (op,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_value_prefix F (ctx,func,cenv,cx) (ty,Literal ann l)
      (sa,sb,op) (es,s0) [] (evaluate_literal l,es,s0)
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  gvs[gas_value_prefix_def, gas_marked_exec_def, gas_marked_path_def,
      literal_read_all_tails]
  >~ [`BoolL b`] >- (Cases_on `b` >> literal_prefix_tac) >>
  literal_prefix_tac
QED

(* A bool, integer or decimal literal annotated with a word type: a Lit,
   no code. *)
Theorem compile_literal_word_sim:
  !ctx func cenv cx ty ann l es.
    is_word_type ann /\
    ((?b. l = BoolL b) \/ (?i. l = IntL i) \/ (?i. l = DecimalL i)) ==>
    expr_sim ctx func cenv cx ty (Literal ann l) es
Proof
  rpt gen_tac >> strip_tac >> irule expr_sim_values >>
  rpt gen_tac >> strip_tac >>
  qexistsl_tac [`[]`, `evaluate_literal l`, `es`, `s0`] >>
  irule literal_word_prefix >> simp[]
QED

