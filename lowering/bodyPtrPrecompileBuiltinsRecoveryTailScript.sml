Theory bodyPtrPrecompileBuiltinsRecoveryTail
Ancestors bodyPtrPrecompileBuiltinsRecoveryResidual
          bodyPtrPrecompileBuiltinsRecoveryValue bodyPtrPrecompileBuiltinsArithmeticTail
          vyperContext vyperValue vyperTyping valueEncoding exprSimWordArgs
          exprSimDefs exprSimProps exprLoweringProps compileEnv rich_list words list

Theorem recovery_arg_typed_encoding:
  ((?k. tv = BaseTV (UintT k) /\ k <= 256) \/
   tv = BaseTV (BytesT (Fixed 32))) /\ value_has_type tv x ==>
  ecrecover_arg_to_num x = SOME (w2n (typed_val_to_w256 tv x))
Proof
  strip_tac
  >- (Cases_on `x` >>
      gvs[value_has_type_def, ecrecover_arg_to_num_def,
          typed_val_to_w256_def, val_to_w256_def] >>
      `Num i < 2 ** 256` by
        (irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists `2 ** k` >> simp[]) >>
      `~(i < 0)` by intLib.ARITH_TAC >>
      gvs[integer_wordTheory.i2w_def, dimword_def,
          fcpLib.INDEX_CONV ``dimindex(:256)``]) >>
  Cases_on `x` >>
  gvs[value_has_type_def, ecrecover_arg_to_num_def,
      typed_val_to_w256_def, PAD_LEFT, PAD_RIGHT]
QED

Theorem recovery_source_value:
  value_has_type (BaseTV (BytesT (Fixed 32))) vh /\
  value_has_type (BaseTV (UintT 256)) vv /\
  value_has_type (BaseTV (UintT 256)) vr /\
  value_has_type (BaseTV (UintT 256)) vq /\
  typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) vh = wh /\
  typed_val_to_w256 (BaseTV (UintT 256)) vv = wv /\
  typed_val_to_w256 (BaseTV (UintT 256)) vr = wr /\
  typed_val_to_w256 (BaseTV (UintT 256)) vq = wq ==>
  builtin_result cx acc ann ECRecover
    [BaseT (BytesT (Fixed 32)); BaseT (UintT 256);
     BaseT (UintT 256); BaseT (UintT 256)] [vh;vv;vr;vq] =
    INL (AddressV (case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n wq) of
      NONE => 0w | SOME addr => addr))
Proof
  strip_tac >>
  `ecrecover_arg_to_num vv = SOME (w2n wv) /\
   ecrecover_arg_to_num vr = SOME (w2n wr) /\
   ecrecover_arg_to_num vq = SOME (w2n wq)` by
    (gvs[] >> rpt conj_tac >> irule recovery_arg_typed_encoding >> simp[]) >>
  Cases_on `vh` >> gvs[value_has_type_def, typed_val_to_w256_def] >>
  simp[builtin_result_def, evaluate_builtin_def, evaluate_ecrecover_def, PAD_RIGHT] >>
  CASE_TAC >> simp[]
QED

Theorem recovery_compiler_append:
  compile_ecrecover h v r q sa = (res,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb
Proof
  strip_tac >> drule bodyPtrPrecompileBuiltinsCompilerStagesTheory.recovery_compiler_stages >>
  strip_tac >>
  imp_res_tac precompile_alloc_compiler_append >>
  imp_res_tac bodyPtrPrecompileBuiltinsCompilerStagesTheory.direct_store_compiler_shape >>
  imp_res_tac bodyPtrPrecompileBuiltinsCompilerStagesTheory.computed_load_suffix_compiler_shape >>
  imp_res_tac bodyPtrPrecompileBuiltinsCompilerStagesTheory.compiler_append_trans >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `same_blocks sa' s0` kall_tac >>
  fs[same_blocks_def]
QED

Theorem recovery_result_posts:
  stmt_state_rel ctx fn cenv cx es' t /\ wb_frame cenv es sf s t /\
  eval_operand res t = SOME (typed_val_to_w256 (BaseTV AddressT) (AddressV addr)) /\
  op_prov G res = NONE /\ op_taint tn res = {} ==>
  vv_post ctx fn cenv cx (Builtin (BaseT AddressT) ECRecover args)
    es sf sb s es' (Value (AddressV addr)) (StackValue (BaseT AddressT) res) t /\
  ptr_val_ok cx (BaseT AddressT) (AddressV addr) res G tn t /\
  (~is_word_type (expr_type (Builtin (BaseT AddressT) ECRecover args)) ==>
   ptr_buf_ok cenv (Builtin (BaseT AddressT) ECRecover args) res G t) /\
  ptr_vv_ok cx (BaseT AddressT) (Value (AddressV addr))
    (StackValue (BaseT AddressT) res) es' G tn t
Proof
  simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def,
       loweringPostsTheory.vv_at_def, loweringPostsTheory.expr_val_rel_def, loweringPostsTheory.expr_val_at_def,
       loweringPostsTheory.wb_frame_def, bodyPtrDefsTheory.ptr_val_ok_def,
       bodyPtrDefsTheory.ptr_vv_ok_def,
       vyperStateTheory.read_result_def, evaluate_type_def,
       is_word_type_def, vyperASTTheory.expr_type_def,
       vyperStateTheory.return_def, exprLoweringTheory.lowered_value_type_def,
       type_memory_bytes_def] >> strip_tac >> first_assum ACCEPT_TAC
QED
