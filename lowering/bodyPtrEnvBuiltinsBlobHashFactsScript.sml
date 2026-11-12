(* Source typing and target read facts for BLOBHASH. *)
Theory bodyPtrEnvBuiltinsBlobHashFacts
Ancestors
  bodyPtrEnvBuiltinsAccountCase exprSimBuiltins exprSimUnopProps
  bodyPtrDefs bodyPtrPreds exprSimDefs exprSimHypsDefs vyperTyping vyperTypeBuiltins
  vyperTypeSystem vyperTypeInvariants vyperInterpreter builtinSimple
  vyperValue vyperState vyperContext vyperAST venomExecSemantics
  venomState venomInst contextCodegenRel codegenRel compileEnv loweringStateRelDefs
  integer_word words list loweringPosts context exprLoweringProps valueEncoding

Theorem blobhash_body_pre_args:
  expr_body_pre cenv cx env (Builtin ann BlobHash args) es ==>
  ?e. args = [e] /\ ann = BaseT (BytesT (Fixed 32)) /\
      expr_type e = BaseT (UintT 256)
Proof
  gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  Cases_on `args` >> gvs[] >> rename1 `h::t` >> Cases_on `t` >> gvs[]
QED

Theorem blobhash_read_typed_step:
  0 <= i /\ i < 2 ** 256 /\ stmt_state_rel ctx fn cenv cx es s /\
  eval_operand arg s = SOME (typed_val_to_w256 (BaseTV (UintT 256)) (IntV i)) ==>
  step_inst_base (mk_inst id BLOBHASH [arg] [out]) s =
    OK (update_var out
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 32)))
        (evaluate_blob_hash cx.txn (Num i))) s)
Proof
  rpt strip_tac >>
  gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
      stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
      typed_val_to_w256_def, evaluate_blob_hash_def] >>
  `?n. i = &n` by metis_tac[integerTheory.NUM_POSINT_EXISTS] >>
  gvs[val_to_w256_def, integer_wordTheory.i2w_pos, wordsTheory.dimword_def,
      PAD_RIGHT, length_word_to_bytes_be, word_of_bytes_be_to_bytes]
QED

Theorem blobhash_source_result:
  unop_result cx (BaseT (BytesT (Fixed 32))) BlobHash tys (IntV i) es =
    INL (evaluate_blob_hash cx.txn (Num i)) /\
  value_has_type (BaseTV (BytesT (Fixed 32)))
    (evaluate_blob_hash cx.txn (Num i))
Proof
  simp[unop_result_def, evaluate_builtin_def, evaluate_blob_hash_def,
       value_has_type_def, PAD_RIGHT, length_word_to_bytes_be]
QED

Theorem blobhash_operand_pre:
  expr_body_pre cenv cx env (Builtin ann BlobHash [e]) es ==>
  expr_body_pre cenv cx env e es
Proof
  strip_tac >> drule blobhash_body_pre_args >> strip_tac >> gvs[] >>
  irule exprSimSourceTheory.expr_body_pre_builtin_typed_arg >> simp[] >>
  conj_tac >- gvs[expr_body_pre_def] >>
  qexistsl_tac [`BaseT (BytesT (Fixed 32))`, `[e]`, `BlobHash`, `es`] >> simp[]
QED
