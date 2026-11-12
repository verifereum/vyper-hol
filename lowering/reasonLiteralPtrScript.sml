(* Literal reason prefixes feed the common checked revert encoder. *)
Theory reasonLiteralPtr
Ancestors reasonLiteralPostPtr reasonMemoryEncoderPtr reasonLiteralBufferPtr
  exprSimLiteralBuffer exprLoweringProps exprLowering context compileEnv
  exprSimHyps exprSimHypsDefs loweringPosts bodyPtrDefs fragGasPathPtr
  fragGasSeqPtr venomState stmtLowering freshWrites vyperInterpreter vyperState
  vyperValue gasCount fragExec exprSimDefs

Theorem reason_literal_encoder_path_ptr:
  compile_bytelike_literal (MAP (n2w o ORD) str) ml sa = (buf,sm) /\
  compile_revert_with_reason cenv
    (LocatedValue (BaseT (StringT (LENGTH str))) (base_ptr buf))
    (BaseT (StringT ml)) (type_memory_bytes cenv (BaseT (StringT ml))) sm = ((),sb) /\
  expr_body_pre cenv cx env (Literal (BaseT (StringT ml)) (StringL str)) es /\
  stmt_state_rel ctx func cenv cx es s /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tnf sf. gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (Abort Revert_abort sf)
Proof
  strip_tac >> drule reason_literal_source_bounds >> strip_tac >>
  `32+32*word_size ml < dimword (:256)` by
    (qpat_x_assum `64+type_memory_bytes _ _ < _` mp_tac >>
     simp[type_memory_bytes_def, vfmConstantsTheory.word_size_def] >> decide_tac) >>
  drule_all reason_literal_buffer_source_post >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule_all reason_literal_buffer_ptr_path >> strip_tac >>
  suspend "encoder"
QED

Resume reason_literal_encoder_path_ptr[encoder]:
  `ci_mono sa sm` by
    metis_tac[ci_mono_compile_bytelike_literal, pairTheory.SND] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `not_fresh_at sm p` by
    (drule reason_literal_compiler_shape >> strip_tac >>
     `ci_mono sh sm` by
       metis_tac[ci_mono_compile_store_byte_chunks, pairTheory.SND] >>
     `not_fresh_at sh p` by gvs[] >>
     irule not_fresh_at_mono >> qexists_tac `sh` >> fs[ci_mono_def]) >>
  `!st. unwrap_value cenv
    (LocatedValue (BaseT (StringT (LENGTH str))) (base_ptr buf)) st = (Var p,st)` by
    simp[unwrap_value_def, base_ptr_def, is_word_type_def, comp_return_def] >>
  `evaluate_type (get_tenv cx) (BaseT (StringT ml)) = SOME (BaseTV (StringT ml))`
    by metis_tac[reason_literal_type_evaluates] >>
  `val_wf (BaseTV (StringT ml)) (StringV str)` by
    fs[expr_post_def, expr_val_at_def, is_word_type_def, vyperASTTheory.expr_type_def] >>
  `~t.vs_halted` by
    (drule gas_path_ptr_ok_not_halted >> simp[]) >>
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    (REWRITE_RULE [GSYM AND_IMP_INTRO] reason_memory_encoder_path_ptr) >>
  rpt (disch_then drule) >> simp[vyperASTTheory.expr_type_def, is_word_type_def] >>
  disch_then (qspecl_then
    [`LocatedValue (BaseT (StringT (LENGTH str))) (base_ptr buf)`, `tn'`,
     `sb`, `sm`, `PG`, `G'`, `D`] mp_tac) >>
  asm_rewrite_tac[] >> simp[] >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >>
  qpat_x_assum `gas_path_ptr D 0 ctx func PG G tn s 0 _ _ _` mp_tac >>
  qpat_x_assum `gas_path_ptr D 0 ctx func PG G' tn' _ 0 _ _ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Finalise reason_literal_encoder_path_ptr

Theorem reason_eval_raise_literal[local]:
  eval_stmt cx (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))) st =
    (INR (AssertException str), st)
Proof
  simp[Once evaluate_def, raise_def] >>
  simp[Once evaluate_def, vyperValueOperationTheory.evaluate_literal_def, bind_def, return_def,
       read_result_def, lift_option_type_def, dest_StringV_def, raise_def]
QED

Theorem compile_raise_reason_lit_frag_ptr:
  expr_body_pre cenv cx env (Literal (BaseT (StringT ml)) (StringL str)) es ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ty
      (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))))
    (eval_stmt cx (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str))))) es
Proof
  strip_tac >> simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, stmtLoweringTheory.declare_stmt_local_def,
       compile_stmt_def, compile_reason_message_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, vyperASTTheory.expr_type_def] >>
  Cases_on `compile_bytelike_literal (MAP (n2w o ORD) str) ml sa` >>
  rename1 `compile_bytelike_literal _ _ sa = (buf, sm)` >>
  Cases_on `compile_revert_with_reason cenv
    (LocatedValue (BaseT (StringT (LENGTH str))) (base_ptr buf))
    (BaseT (StringT ml)) (type_memory_bytes cenv (BaseT (StringT ml))) sm` >>
  rename1 `compile_revert_with_reason _ _ _ _ sm = (u, sf)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  suspend "literal"
QED

Resume compile_raise_reason_lit_frag_ptr[literal]:
  `ci_mono sa sm` by
    metis_tac[ci_mono_compile_bytelike_literal, pairTheory.SND] >>
  `cs_extends sa sm` by fs[ci_mono_def] >>
  `cs_extends sm sb` by
    (drule stmtSimReasonTheory.compile_revert_reason_split_certificate >>
     strip_tac >>
     qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     simp[unwrap_value_def, base_ptr_def, is_word_type_def, comp_return_def] >>
     strip_tac >> gvs[] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all reason_literal_encoder_path_ptr >>
  disch_then (qspecl_then [`tn0`, `PG`, `G0`, `cx_dead cx`] strip_assume_tac) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def, reason_eval_raise_literal] >>
  qexistsl_tac [`INR (AssertException str)`, `es`, `Gf`, `tnf`] >>
  qexists_tac `Abort Revert_abort sf` >>
  simp[fragExecTheory.exit_result_def, stmt_exit_ptr_def,
       exprSimDefsTheory.expr_exit_def]
QED

Finalise compile_raise_reason_lit_frag_ptr
