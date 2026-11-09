Theory bodyPtrPrecompileBuiltinsArithmeticTail
Ancestors bodyPtrPrecompileBuiltinsArithmeticResidual
          bodyPtrPrecompileBuiltinsCompilerStages builtinMisc context emitHelper
          exprLoweringProps rich_list compileEnv exprSimPrecompiles
          bodyPtrPrecompileBuiltinsArithmeticSource valueEncodingProps bodyPtrDefs ptrDiscipline exprSimDefs exprSimProps valueEncoding
          vyperValue vyperTyping exprSimWordArgs venomState venomExecSemantics

Theorem precompile_alloc_compiler_append:
  compile_alloc_buffer n sa = (buf,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND1, same_blocks_def]
QED

Theorem precompile_suffix_same_blocks:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit outsz];
      emit_void ASSERT [success]; return op od) sa = (res,sb) ==>
  same_blocks sa sb
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[same_blocks_def]
QED

Theorem ecmul_compiler_append:
  compile_ecmul_point p k sa = (res,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb
Proof
  strip_tac >> drule ecmul_compiler_stages >> strip_tac >>
  imp_res_tac precompile_alloc_compiler_append >>
  imp_res_tac precompile_suffix_same_blocks >>
  imp_res_tac compiler_append_trans >>
  gvs[same_blocks_def]
QED

Theorem ecadd_compiler_append:
  compile_ecadd_points p q sa = (res,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb
Proof
  strip_tac >> drule ecadd_compiler_stages >> strip_tac >>
  imp_res_tac precompile_alloc_compiler_append >>
  imp_res_tac precompile_suffix_same_blocks >>
  imp_res_tac compiler_append_trans >>
  gvs[same_blocks_def]
QED

Theorem precompile_final_cursor:
  sb.cs_current_insts = sf.cs_current_insts ++ emitted_insts sf sb /\
  same_blocks sf sb /\ s.vs_current_bb = sf.cs_current_bb /\
  s.vs_inst_idx = LENGTH sf.cs_current_insts /\
  t.vs_current_bb = s.vs_current_bb /\
  t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sf sb) ==>
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  simp[same_blocks_def] >> strip_tac >> simp[]
QED

Theorem ecmul_source_tail_ptr_path:
  compile_ecmul_point point scalar sf = (res,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ ~ctx_has_dalloca ctx /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts fn)) /\
  ghost_inv d cenv cx es G tn s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v point s /\
  ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v point G tn s /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v /\
  op_taint tn scalar = {} /\ (!l. scalar <> Label l) /\
  (!p. MEM (Var p) [point;scalar] ==> not_fresh_at sf p) /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sf sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v point s /\
  value_has_type (BaseTV (UintT 256)) k /\
  expr_val_rel cx (BaseT (UintT 256)) k scalar s /\
  fn_has_code sf sb fn /\ s.vs_current_bb = sf.cs_current_bb /\
  s.vs_inst_idx = LENGTH sf.cs_current_insts /\
  ec_source_tail cx ann ECMul tys [v;k] es = (r,es') ==>
  ?n result G' tn'. gas_path_ptr D 0 ctx fn PG G tn s n G' tn' result /\
   ((?t value. result = OK t /\ r = INL (Value value) /\
      vv_post ctx fn cenv cx (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul args)
        es sf sb s es' (Value value)
        (FST (as_ptr_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) LocMemory (res,sb))) t /\
      ghost_inv d cenv cx es' G' tn' t /\ ghost_kept cenv es sf G tn s G' tn' /\
      ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) value res G' tn' t /\
      ptr_buf_ok cenv (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul args) res G' t /\
      ptr_vv_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) (Value value)
        (FST (as_ptr_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) LocMemory (res,sb))) es' G' tn' t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    \/ (exit_result result /\ expr_exit r result))
Proof
  strip_tac >>
  drule_all (REWRITE_RULE [mem_word_at_eq_mload] ecmul_memory_semantics) >> strip_tac >>
  `es.outcomes = SOME s.vs_outcomes` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `ec_source_tail _ _ _ _ _ _ = _` mp_tac >>
  simp[arithmetic_source_tail_cases, builtin_result_def,
       vyperContextTheory.evaluate_builtin_def] >>
  Cases_on `vfmExecution$ecmul (w2n (mload (w2n point') s),
    w2n (mload (w2n point'+32) s)) (w2n sw)`
  >- (simp[] >> strip_tac >> suspend "invalid") >>
  PairCases_on `x` >> simp[] >>
  Cases_on `s.vs_outcomes`
  >- (simp[] >> strip_tac >> suspend "empty") >>
  rename1 `s.vs_outcomes = co::rest` >> Cases_on `co.co_success`
  >- (simp[] >> strip_tac >> suspend "success") >>
  simp[] >> strip_tac >> suspend "failed"
QED

Resume ecmul_source_tail_ptr_path[invalid]:
  drule_all (cj 1 (PURE_REWRITE_RULE [LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
    DISJ_IMP_THM] ecmul_residual_abort)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  simp[expr_exit_def, fragExecTheory.exit_result_def]
QED

Resume ecmul_source_tail_ptr_path[empty]:
  drule_all (cj 2 (PURE_REWRITE_RULE [LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
    DISJ_IMP_THM] ecmul_residual_abort)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  simp[expr_exit_def, fragExecTheory.exit_result_def]
QED

Resume ecmul_source_tail_ptr_path[failed]:
  SUBGOAL_THEN ``?co rest. s.vs_outcomes = co::rest /\ ~co.co_success`` assume_tac
  >- metis_tac[] >>
  drule_all (cj 3 (PURE_REWRITE_RULE [LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
    DISJ_IMP_THM] ecmul_residual_abort)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  simp[expr_exit_def, fragExecTheory.exit_result_def]
QED

Resume ecmul_source_tail_ptr_path[success]:
  SUBGOAL_THEN ``?co rest. s.vs_outcomes = co::rest /\ co.co_success`` assume_tac
  >- metis_tac[] >>
  drule_all ecmul_residual_success >>
  disch_then (qspecl_then [`args`,`PG`] strip_assume_tac) >>
  drule ecmul_compiler_append >> strip_tac >>
  drule_all precompile_final_cursor >> strip_tac >>
  goal_assum (drule_at Any) >> gvs[] >>
  disj1_tac >> qexists `mk_ec_result (x0,x1)` >> simp[]
QED
Finalise ecmul_source_tail_ptr_path

Theorem ecadd_source_tail_ptr_path:
  compile_ecadd_points point other sf = (res,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ ~ctx_has_dalloca ctx /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts fn)) /\
  ghost_inv d cenv cx es G tn s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es vp point s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es vq other s /\
  ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) vp point G tn s /\
  ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) vq other G tn s /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) vp /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) vq /\
  (!p. MEM (Var p) [point;other] ==> not_fresh_at sf p) /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sf sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) vp point s /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) vq other s /\
  fn_has_code sf sb fn /\ s.vs_current_bb = sf.cs_current_bb /\
  s.vs_inst_idx = LENGTH sf.cs_current_insts /\
  ec_source_tail cx ann ECAdd tys [vp;vq] es = (r,es') ==>
  ?n result G' tn'. gas_path_ptr D 0 ctx fn PG G tn s n G' tn' result /\
   ((?t value. result = OK t /\ r = INL (Value value) /\
      vv_post ctx fn cenv cx (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd args)
        es sf sb s es' (Value value)
        (FST (as_ptr_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) LocMemory (res,sb))) t /\
      ghost_inv d cenv cx es' G' tn' t /\ ghost_kept cenv es sf G tn s G' tn' /\
      ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) value res G' tn' t /\
      ptr_buf_ok cenv (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd args) res G' t /\
      ptr_vv_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) (Value value)
        (FST (as_ptr_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) LocMemory (res,sb))) es' G' tn' t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    \/ (exit_result result /\ expr_exit r result))
Proof
  strip_tac >>
  qpat_assum `value_has_type _ vp`
    (mp_then Any mp_tac (REWRITE_RULE [mem_word_at_eq_mload] ecadd_memory_semantics)) >>
  disch_then drule_all >> strip_tac >>
  `es.outcomes = SOME s.vs_outcomes` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `ec_source_tail _ _ _ _ _ _ = _` mp_tac >>
  simp[arithmetic_source_tail_cases, builtin_result_def,
       vyperContextTheory.evaluate_builtin_def] >>
  rename1 `eval_operand point s = SOME a1` >>
  rename1 `eval_operand other s = SOME a2` >>
  Cases_on `vfmExecution$ecadd (w2n (mload (w2n a1) s),
    w2n (mload (w2n a1+32) s))
    (w2n (mload (w2n a2) s),w2n (mload (w2n a2+32) s))`
  >- (simp[] >> strip_tac >> suspend "invalid") >>
  PairCases_on `x` >> simp[] >>
  Cases_on `s.vs_outcomes`
  >- (simp[] >> strip_tac >> suspend "empty") >>
  rename1 `s.vs_outcomes = co::rest` >> Cases_on `co.co_success`
  >- (simp[] >> strip_tac >> suspend "success") >>
  simp[] >> strip_tac >> suspend "failed"
QED

Resume ecadd_source_tail_ptr_path[invalid]:
  drule_all (cj 1 (PURE_REWRITE_RULE [LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
    DISJ_IMP_THM] ecadd_residual_abort)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  simp[expr_exit_def, fragExecTheory.exit_result_def]
QED

Resume ecadd_source_tail_ptr_path[empty]:
  drule_all (cj 2 (PURE_REWRITE_RULE [LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
    DISJ_IMP_THM] ecadd_residual_abort)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  simp[expr_exit_def, fragExecTheory.exit_result_def]
QED

Resume ecadd_source_tail_ptr_path[failed]:
  SUBGOAL_THEN ``?co rest. s.vs_outcomes = co::rest /\ ~co.co_success`` assume_tac
  >- metis_tac[] >>
  drule_all (cj 3 (PURE_REWRITE_RULE [LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
    DISJ_IMP_THM] ecadd_residual_abort)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  simp[expr_exit_def, fragExecTheory.exit_result_def]
QED

Resume ecadd_source_tail_ptr_path[success]:
  SUBGOAL_THEN ``?co rest. s.vs_outcomes = co::rest /\ co.co_success`` assume_tac
  >- metis_tac[] >>
  drule_all ecadd_residual_success >>
  disch_then (qspecl_then [`args`,`PG`] strip_assume_tac) >>
  drule ecadd_compiler_append >> strip_tac >>
  drule_all precompile_final_cursor >> strip_tac >>
  goal_assum (drule_at Any) >> gvs[] >>
  disj1_tac >> qexists `mk_ec_result (x0,x1)` >> simp[]
QED
Finalise ecadd_source_tail_ptr_path
