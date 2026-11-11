Theory bodyPtrPrecompileBuiltinsRecoveryTail
Ancestors bodyPtrPrecompileBuiltinsRecoveryResidual
          bodyPtrPrecompileBuiltinsRecoveryValue bodyPtrPrecompileBuiltinsArithmeticTail
          vyperContext vyperValue vyperTyping valueEncoding exprSimWordArgs
          exprSimDefs exprSimProps exprLoweringProps compileEnv loweringStateRelDefs rich_list words list

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
  (tv = BaseT (UintT 8) \/ tv = BaseT (UintT 256) \/
   tv = BaseT (BytesT (Fixed 32))) /\
  (tr = BaseT (UintT 256) \/ tr = BaseT (BytesT (Fixed 32))) /\
  (tq = BaseT (UintT 256) \/ tq = BaseT (BytesT (Fixed 32))) /\
  evaluate_type (get_tenv cx) tv = SOME tvv /\
  evaluate_type (get_tenv cx) tr = SOME trr /\
  evaluate_type (get_tenv cx) tq = SOME tqq /\
  value_has_type tvv vv /\ value_has_type trr vr /\ value_has_type tqq vq /\
  typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) vh = wh /\
  typed_val_to_w256 tvv vv = wv /\
  typed_val_to_w256 trr vr = wr /\
  typed_val_to_w256 tqq vq = wq ==>
  builtin_result cx acc ann ECRecover
    [BaseT (BytesT (Fixed 32)); tv;tr;tq] [vh;vv;vr;vq] =
    INL (AddressV (case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n wq) of
      NONE => 0w | SOME addr => addr))
Proof
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `ecrecover_arg_to_num vv = SOME (w2n wv) /\
   ecrecover_arg_to_num vr = SOME (w2n wr) /\
   ecrecover_arg_to_num vq = SOME (w2n wq)` by
    (gvs[evaluate_type_def] >> rpt conj_tac >>
     irule recovery_arg_typed_encoding >> simp[]) >>
  ntac 3 (qpat_x_assum `_ \/ _` kall_tac) >>
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
  stmt_state_rel ctx fn cenv cx es' t /\ wb_frame cenv es es' sf s t /\
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

Theorem recovery_source_tail_ptr_path:
  compile_ecrecover h v rr q sf = (res,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ ~ctx_has_dalloca ctx /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts fn)) /\
  ghost_inv d cenv cx es G tn s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand rr s = SOME wr /\ eval_operand q s = SOME wq /\
  EVERY (\x. op_taint tn x = {} /\ (!l. x <> Label l) /\
    (!p. x = Var p ==> not_fresh_at sf p)) [h;v;rr;q] /\
  allocas_from 0 s /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sf sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  value_has_type (BaseTV (BytesT (Fixed 32))) vh /\
  (tv = BaseT (UintT 8) \/ tv = BaseT (UintT 256) \/
   tv = BaseT (BytesT (Fixed 32))) /\
  (tr = BaseT (UintT 256) \/ tr = BaseT (BytesT (Fixed 32))) /\
  (tq = BaseT (UintT 256) \/ tq = BaseT (BytesT (Fixed 32))) /\
  evaluate_type (get_tenv cx) tv = SOME tvv /\
  evaluate_type (get_tenv cx) tr = SOME trr /\
  evaluate_type (get_tenv cx) tq = SOME tqq /\
  value_has_type tvv vv /\ value_has_type trr vr /\ value_has_type tqq vq /\
  typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) vh = wh /\
  typed_val_to_w256 tvv vv = wv /\
  typed_val_to_w256 trr vr = wr /\
  typed_val_to_w256 tqq vq = wq /\
  s.vs_current_bb = sf.cs_current_bb /\
  s.vs_inst_idx = LENGTH sf.cs_current_insts /\
  ec_source_tail cx ann ECRecover
    [BaseT (BytesT (Fixed 32)); tv;tr;tq] [vh;vv;vr;vq] es = (r,es') ==>
  ?n result G' tn'. gas_path_ptr D 0 ctx fn PG G tn s n G' tn' result /\
   ((?t value. result = OK t /\ r = INL (Value value) /\
      vv_post ctx fn cenv cx (Builtin (BaseT AddressT) ECRecover args)
        es sf sb s es' (Value value) (StackValue (BaseT AddressT) res) t /\
      ghost_inv d cenv cx es' G' tn' t /\ ghost_kept cenv es sf G tn s G' tn' /\
      ptr_val_ok cx (BaseT AddressT) value res G' tn' t /\
      (~is_word_type (expr_type (Builtin (BaseT AddressT) ECRecover args)) ==>
       ptr_buf_ok cenv (Builtin (BaseT AddressT) ECRecover args) res G' t) /\
      ptr_vv_ok cx (BaseT AddressT) (Value value)
        (StackValue (BaseT AddressT) res) es' G' tn' t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    \/ (exit_result result /\ expr_exit r result))
Proof
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `builtin_result cx es.accounts ann ECRecover
    [BaseT (BytesT (Fixed 32)); tv;tr;tq] [vh;vv;vr;vq] =
    INL (AddressV (case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n wq) of
      NONE => 0w | SOME addr => addr))` by
    (irule recovery_source_value >> simp[]) >>
  `es.outcomes = SOME s.vs_outcomes` by gvs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `ec_source_tail _ _ _ _ _ _ = _` mp_tac >>
  simp[exprSimECArithTheory.ec_source_tail_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
       vyperInterpreterTheory.precompile_call_success_def,
       vyperInterpreterTheory.precompile_builtin_def] >>
  Cases_on `s.vs_outcomes`
  >- (simp[vyperStateTheory.check_def, vyperStateTheory.assert_def,
           vyperStateTheory.raise_def] >> strip_tac >> suspend "empty") >>
  rename1 `s.vs_outcomes = co::rest` >> Cases_on `co.co_success` >>
  simp[vyperStateTheory.check_def, vyperStateTheory.assert_def,
       vyperStateTheory.raise_def, vyperStateTheory.return_def]
  >- (strip_tac >> suspend "success") >>
  strip_tac >> suspend "failed"
QED

Resume recovery_source_tail_ptr_path[empty]:
  `~(?co rest. s.vs_outcomes = co::rest /\ co.co_success)` by simp[] >>
  drule_all recovery_residual_oracle_failure >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[expr_exit_def, fragExecTheory.exit_result_def]
QED

Resume recovery_source_tail_ptr_path[failed]:
  `~(?co rest. s.vs_outcomes = co::rest /\ co.co_success)` by simp[] >>
  drule_all recovery_residual_oracle_failure >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[expr_exit_def, fragExecTheory.exit_result_def]
QED

Resume recovery_source_tail_ptr_path[success]:
  SUBGOAL_THEN ``?co rest. s.vs_outcomes = co::rest /\ co.co_success`` assume_tac
  >- metis_tac[] >>
  drule_all recovery_residual_success >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule recovery_compiler_append >> strip_tac >>
  drule_all precompile_final_cursor >> strip_tac >>
  drule_all recovery_result_posts >>
  disch_then (qspecl_then [`sb`,`args`] strip_assume_tac) >>
  goal_assum (drule_at Any) >> gvs[] >>
  disj1_tac >> goal_assum (drule_at Any) >> simp[]
QED
Finalise recovery_source_tail_ptr_path

