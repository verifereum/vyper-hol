Theory bodyMemBiBlobHashSim
Ancestors
  bodyMemBiBlobHashFrag bodyUnopFragMemory exprSimBuiltins exprSimAccounts
  exprSimMemDefs exprSimMemoryStack exprSimSource exprSimUnopProps
  exprSimProps exprSimDefs exprSimHypsDefs loweringPosts
  exprLowering emitHelperProps exprLoweringProps exprUnopSimDefs
  builtinSimple builtinProps vyperAST vyperValue vyperTyping
  vyperInterpreter vyperValueOperation vyperState vyperContext
  compileEnv valueEncoding integer arithmetic list
Libs
  intLib

Theorem compile_blobhash_sim_mem:
  !ctx func cenv cx env ty e es.
    expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT 256) /\
    expr_sim_mem ctx func cenv cx ty e es ==>
    expr_sim_mem ctx func cenv cx ty
      (Builtin (BaseT (BytesT (Fixed 32))) BlobHash [e]) es
Proof
  rpt strip_tac >>
  irule (Q.INST [`ty1` |-> `ty`, `f` |-> `\x. emit_op BLOBHASH [x]`]
    (SPEC_ALL compile_unop_sim_mem)) >>
  simp[is_word_type_def, builtin_args_length_ok_def] >>
  rpt conj_tac
  >~ [`lower_value _ _ _ (Builtin _ _ _) _ = _ ==> _`]
  >- (rpt strip_tac >> drule lower_value_blobhash >> simp[])
  >~ [`lower_value _ _ _ e _ = _ ==> _`]
  >- (rpt gen_tac >> strip_tac >>
      drule expr_body_pre_lower_value_word_shape >> disch_then drule >>
      simp[is_word_type_def])
  >~ [`emit_op _ _ _ = _ ==> _`]
  >- (rpt gen_tac >> strip_tac >> drule emit_op_extends_next_var >> simp[]) >>
  rpt strip_tac >>
  qspecl_then [`cenv`, `cx`, `env`, `e`, `es with gas_obs := gs1`, `v1`, `es1`]
    mp_tac expr_body_pre_word_value >>
  simp[is_word_type_def] >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  Cases_on `v1` >> gvs[value_has_type_def] >>
  irule compile_blobhash_frag_mem >>
  `?n. i = &n` by metis_tac[integerTheory.NUM_POSINT_EXISTS] >> gvs[]
QED

Theorem compile_blobhash_vv_sim_mem:
  !ctx func cenv cx env ty e es.
    expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT 256) /\
    expr_sim_mem ctx func cenv cx ty e es ==>
    expr_vv_sim_mem ctx func cenv cx ty
      (Builtin (BaseT (BytesT (Fixed 32))) BlobHash [e]) es
Proof
  rpt strip_tac >>
  irule body_expr_vv_sim_mem_stack_word >>
  rpt conj_tac
  >~ [`is_word_type`] >- simp[vyperASTTheory.expr_type_def, is_word_type_def]
  >~ [`compile_expr`] >- simp[compile_blobhash_stack]
  >~ [`eval_expr`] >- metis_tac[eval_expr_builtin_value] >>
  irule compile_blobhash_sim_mem >> metis_tac[]
QED
