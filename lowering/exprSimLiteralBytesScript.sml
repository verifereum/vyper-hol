(* Counted forcing of address and fixed-byte literals. *)
Theory exprSimLiteralBytes
Ancestors
  exprSimHypsDefs exprSimProps exprSimDefs exprSimValues exprSimLiteralWord loweringPosts
  gasOutcome gasSummary gasNormalPrefix fragGasPath fragGasMode
  list finite_map exprLowering exprLoweringProps compileEnv
  vyperAST vyperInterpreter vyperState vyperValue vyperValueOperation vyperTypeSystem
  valueEncoding valueEncodingProofs fragExec venomInst venomState

val literal_bytes_word_tac =
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      compile_literal_vv_def, unwrap_value_def, evaluate_literal_def,
      vyperASTTheory.expr_type_def] >>
  conj_tac >- (irule (cj 1 gas_path_rules) >> simp[]) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def];

Theorem literal_bytes_word_prefix[local]:
  !ctx func cenv cx env ty ann bs es sa sb op s0.
    expr_sim_pre cenv cx env (Literal ann (BytesL bs)) es /\
    is_word_type ann /\
    lower_value compile_expr cenv ty (Literal ann (BytesL bs)) sa = (op,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_value_prefix F (ctx,func,cenv,cx) (ty,Literal ann (BytesL bs))
      (sa,sb,op) (es,s0) [] (evaluate_literal (BytesL bs),es,s0)
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  gvs[gas_value_prefix_def, gas_marked_exec_def, gas_marked_path_def,
      literal_read_all_tails, expr_sim_pre_def, well_typed_expr_def] >>
  Cases_on `ann` >> gvs[well_typed_literal_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[well_typed_literal_def, is_word_type_def]
  >~ [`BytesT bd`] >- (Cases_on `bd` >> gvs[is_word_type_def] >>
                       literal_bytes_word_tac) >>
  literal_bytes_word_tac
QED

(* An address or bytesN literal: a Lit of its typed encoding, the 20 bytes
   of an address right-aligned and the bytes of a bytesN left-aligned, as
   expr_val_rel has them.  No code. *)
Theorem compile_literal_bytes_word_sim:
  !ctx func cenv cx env ty ann bs es.
    expr_sim_pre cenv cx env (Literal ann (BytesL bs)) es /\
    is_word_type ann ==>
    expr_sim ctx func cenv cx ty (Literal ann (BytesL bs)) es
Proof
  rpt gen_tac >> strip_tac >> irule expr_sim_values >>
  rpt gen_tac >> strip_tac >>
  qexistsl_tac [`[]`, `evaluate_literal (BytesL bs)`, `es`, `s0`] >>
  irule literal_bytes_word_prefix >> simp[] >> metis_tac[]
QED


