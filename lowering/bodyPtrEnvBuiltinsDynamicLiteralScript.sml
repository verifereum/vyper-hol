(* Literal MethodId consumer boundaries. *)
Theory bodyPtrEnvBuiltinsDynamicLiteral
Ancestors bodyPtrEnvBuiltinsMethodFolded bodyPtrEnvBuiltinsFoldedPost bodyPtrEnvBuiltinsFoldedCounted
  bodyPtrEnvBuiltinsMethodShape bodyPtrEnvBuiltinsMethodLiteral
  exprSimHash exprLowering exprLoweringProps compileEnv context emitHelper
  fragExec vyperAST vyperValue vyperInterpreter vyperState
  words list rich_list bodyPtrDefs fragGasPathPtr gasSummary loweringPosts
  bodyPtrEnvBuiltinsSelectorCounted ghostPcTransportPtr ptrDiscipline
  entrySinkExtraction venomInst venomState stmtFragPtr exprSimWordArgs
  bodyPtrEnvBuiltinsBoundary

Theorem method_literal_dynamic_compile:
  method_id_literal (Literal la l) = SOME bs /\
  compile_expr cenv ty
    (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) sa = (vv,sb) ==>
  ?buf. compile_bytelike_literal (TAKE 4 (Keccak_256_w64 bs)) 4 sa = (buf,sb) /\
    vv = LocatedValue (BaseT (BytesT (Dynamic 4))) (base_ptr buf)
Proof
  strip_tac >> drule compile_expr_method_id_literal >>
  disch_then (qspecl_then [`cenv`, `ty`, `BaseT (BytesT (Dynamic 4))`, `sa`]
    assume_tac) >>
  gvs[compile_literal_vv_def, method_id_digest_length, comp_bind_def,
    comp_return_def] >> pairarg_tac >> gvs[]
QED

Theorem method_literal_dynamic_source:
  method_id_literal (Literal la l) = SOME bs ==>
  eval_expr cx (Builtin ann MethodId [Literal la l]) es =
    (INL (Value (BytesV (TAKE 4 (Keccak_256_w64 bs)))), es)
Proof
  strip_tac >>
  Cases_on `eval_expr cx (Builtin ann MethodId [Literal la l]) es` >>
  drule_all eval_expr_method_id_literal >> simp[]
QED

Theorem folded_selector_prefix:
  LENGTH (bs:word8 list) = 4 /\
  compile_bytelike_literal bs 4 sa = (buf,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >> drule_all folded_selector_code >> strip_tac >>
  gvs[fn_has_code_def] >>
  gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_APPEND]
QED

Theorem method_literal_dynamic_vv_sim_ptr:
  method_id_literal (Literal la l) = SOME bs ==>
  expr_vv_sim_ptr d ctx PG fn cenv cx ty
    (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) es
Proof
  strip_tac >> rw[expr_vv_sim_ptr_def] >>
  drule_all method_literal_dynamic_compile >> strip_tac >> gvs[] >>
  `LENGTH (TAKE 4 (Keccak_256_w64 bs)) = 4` by
    simp[method_id_digest_length] >>
  drule_all folded_selector_run_post >>
  disch_then (qspec_then `[Literal la l]` strip_assume_tac) >>
  drule_all folded_selector_prefix >> strip_tac >>
  drule_all folded_selector_counted >>
  disch_then (qspecl_then [`[Literal la l]`, `PG`, `cx_dead cx`]
    strip_assume_tac) >>
  `t.vs_current_bb = s0.vs_current_bb` by
    (irule (cj 2 run_inst_seq_preserves_entry_control) >>
     goal_assum (drule_at Any) >>
     drule_all folded_selector_code >> strip_tac >>
     simp[mk_inst_def, is_terminator_def]) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (Value (BytesV (TAKE 4 (Keccak_256_w64 bs))))`,
    `es`, `G'`, `tn'`, `OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[method_literal_dynamic_source, gas_explicit_def] >>
  conj_tac >- (gvs[vv_post_def, vv_holds_def, vv_at_def,
    stmt_state_rel_gas_obs, base_ptr_def, read_result_def, return_def,
    expr_type_def] >> first_assum ACCEPT_TAC) >>
  conj_tac >- (drule_all folded_selector_code >> strip_tac >> simp[]) >>
  gvs[ghost_inv_gas_obs, ptr_vv_ok_def, base_ptr_def, expr_type_def,
    read_result_def, return_def, ptr_val_ok_def, is_word_type_def,
    ptr_mem_ok_def]
QED

Theorem body_method_literal_ptr_case:
  method_id_literal (Literal la l) = SOME bs ==>
  body_expr_ptr_ok cx (Builtin ann MethodId [Literal la l])
Proof
  strip_tac >> irule body_expr_ptr_of_vv >> rpt gen_tac >> strip_tac >>
  drule_all method_id_builtin_pre_shape >> strip_tac >> gvs[]
  >- (irule method_literal_dynamic_vv_sim_ptr >> simp[]) >>
  irule method_literal_word_vv_sim_ptr >> simp[]
QED
