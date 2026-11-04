(* Counted simulation for word literals. *)
Theory exprSimLiteralWord
Ancestors
  exprSimProps
  exprSimDefs exprSimStack exprSimValues
  loweringPosts
  list rich_list finite_map pred_set
  fragExec varsExt loweringSlice localPtrsProps venomMemDefs
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperValueOperation vyperContext
  valueEncoding valueEncodingProofs vyperTypeSystem
  venomExecSemantics venomInst venomState
  vyperLookupStorage vyperStorageBackend

val literal_word_tac =
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      compile_literal_vv_def, unwrap_value_def, evaluate_literal_def] >>
  irule frag_exec_refl >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def,
       eval_operand_def, typed_val_to_w256_word_value, word_value_def] >>
  simp[val_to_w256_def];

(* A bool, integer or decimal literal annotated with a word type: a Lit,
   no code. *)
Theorem compile_literal_word_sim:
  !ctx func cenv cx ty ann l es.
    is_word_type ann /\
    ((?b. l = BoolL b) \/ (?i. l = IntL i) \/ (?i. l = DecimalL i)) ==>
    expr_sim ctx func cenv cx ty (Literal ann l) es
Proof
  rw[expr_sim_def] >> gvs[Once evaluate_def, bind_def, read_result_def, return_def]
  >~ [`BoolL b`] >- (Cases_on `b` >> literal_word_tac) >>
  literal_word_tac
QED
