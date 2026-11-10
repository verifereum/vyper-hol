Theory bodyLiteralMemory
Ancestors
  exprSimMemDefs exprSimHypsDefs exprSimProps
  exprLowering exprLoweringProps fragExecMem
  gasSummary fragGasMode fragGasPathMem gasNormalPrefix loweringPosts
  valueEncodingProofs exprSimMemoryStack exprSimMemoryValues
  vyperAST vyperInterpreter vyperTyping valueEncoding
  vyperTypeSystem compileEnv context vyperState exprSimDefs
  vyperValueOperation venomState vyperValue loweringSlice

Theorem body_literal_word_compile[local]:
  expr_sim_pre cenv cx env (Literal ann l) es /\ is_word_type ann ==>
  ?op. compile_expr cenv ty (Literal ann l) sa = (StackValue ann op,sa)
Proof
  strip_tac >>
  `~(?str. l = StringL str)` by
    (strip_tac >> gvs[expr_sim_pre_def, well_typed_expr_def] >>
     Cases_on `ann` >> gvs[well_typed_literal_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[well_typed_literal_def, is_word_type_def]) >>
  Cases_on `l` >> gvs[]
  >~ [`BytesL bs`]
  >- (`!n. ann <> BaseT (BytesT (Dynamic n))` by
        (rpt strip_tac >> gvs[is_word_type_def]) >>
      simp[compile_expr_def, expr_type_def] >> irule compile_literal_bytes_stack >> simp[]) 
  >~ [`BoolL b`]
  >- (Cases_on `b` >> simp[compile_expr_def, compile_literal_vv_def, expr_type_def, comp_return_def]) >>
  simp[compile_expr_def, compile_literal_vv_def, expr_type_def, comp_return_def]
QED



Theorem body_literal_mem_exec[local]:
  ~s0.vs_halted ==>
  gas_marked_exec T (ctx,func)
    (bind (eval_expr cx (Literal ann l)) (read_result cx))
    (es,s0) [] (INL (evaluate_literal l)) es (OK s0)
Proof
  simp[gas_marked_exec_def, gas_marked_path_def,
       Once evaluate_def, bind_def, read_result_def, return_def] >>
  metis_tac[gas_path_mem_rules]
QED

val body_literal_prefix_tac =
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      compile_literal_vv_def, unwrap_value_def, evaluate_literal_def,
      expr_type_def] >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       expr_type_def, eval_operand_def,
       typed_val_to_w256_word_value, word_value_def, val_to_w256_def,
       is_word_type_def, evaluate_type_def];

Theorem body_literal_word_mem_prefix:
  expr_sim_pre cenv cx env (Literal ann l) es /\ is_word_type ann /\
  lower_value compile_expr cenv ty (Literal ann l) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_value_prefix T (ctx,func,cenv,cx) (ty,Literal ann l)
    (sa,sb,op) (es,s0) [] (evaluate_literal l,es,s0)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[gas_value_prefix_def, body_literal_mem_exec] >>
  gvs[expr_sim_pre_def, well_typed_expr_def] >>
  Cases_on `l` >> gvs[well_typed_literal_def]
  >~ [`BoolL b`] >- (Cases_on `b` >> body_literal_prefix_tac)
  >~ [`IntL i`] >- body_literal_prefix_tac
  >~ [`DecimalL i`] >- body_literal_prefix_tac >>
  Cases_on `ann` >> gvs[well_typed_literal_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[well_typed_literal_def, is_word_type_def]
  >~ [`BytesT bd`] >- (Cases_on `bd` >> gvs[is_word_type_def] >>
      body_literal_prefix_tac) >>
  body_literal_prefix_tac
QED

(* Prior successful uncounted proof, retained for reference.
val literal_word_vv_mem_tac =
  gvs[compile_expr_def, comp_return_def, compile_literal_vv_def,
      evaluate_literal_def, expr_type_def] >>
  irule frag_exec_mem_refl >>
  simp[vv_post_def, vv_holds_def, vv_at_def, read_result_def, return_def, vv_operand_def,
       vv_location_def, expr_val_rel_def, expr_val_at_def, expr_type_def,
       eval_operand_def, typed_val_to_w256_word_value, word_value_def] >>
  simp[val_to_w256_def, is_word_type_def, evaluate_type_def];

Theorem compile_literal_word_body_vv_sim_mem:
  !ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es /\ is_word_type ann ==>
    expr_vv_sim_mem ctx func cenv cx ty (Literal ann l) es
Proof
  rpt gen_tac >> strip_tac >>
  rw[expr_vv_sim_mem_def] >>
  gvs[Once evaluate_def, return_def, expr_sim_pre_def, well_typed_expr_def] >>
  Cases_on `l` >> gvs[well_typed_literal_def]
  >~ [`BoolL b`] >- (Cases_on `b` >> literal_word_vv_mem_tac)
  >~ [`IntL i`] >- literal_word_vv_mem_tac
  >~ [`DecimalL i`] >- literal_word_vv_mem_tac >>
  Cases_on `ann` >> gvs[well_typed_literal_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[well_typed_literal_def, is_word_type_def]
  >~ [`BytesT bd`] >- (Cases_on `bd` >> gvs[is_word_type_def] >>
      literal_word_vv_mem_tac) >>
  literal_word_vv_mem_tac
QED

*)

Theorem compile_literal_word_body_vv_sim_mem:
  !ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es /\ is_word_type ann ==>
    expr_vv_sim_mem ctx func cenv cx ty (Literal ann l) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_sim_mem ctx func cenv cx ty (Literal ann l) es` by
    (irule expr_sim_mem_word_values >>
     reverse conj_tac >- simp[vyperASTTheory.expr_type_def] >>
     rpt gen_tac >> strip_tac >>
     qexistsl_tac [`[]`, `evaluate_literal l`, `es`, `s0`] >>
     irule body_literal_word_mem_prefix >> metis_tac[]) >>
  `is_word_type (expr_type (Literal ann l))` by
    gvs[vyperASTTheory.expr_type_def] >>
  drule_then irule body_expr_vv_sim_mem_stack_word >>
  simp[] >> conj_tac
  >- metis_tac[body_literal_word_compile] >>
  simp[Once evaluate_def, return_def] >> metis_tac[]
QED

