Theory bodyPtrCodeSliceSelf
Ancestors
  bodyPtrCodeSliceSelfOperands bodyPtrCodeSliceSelfContinue bodyPtrPreds bodyPtrDefs
  exprPtrUnwrap exprSimSliceSelfCode exprSimSliceSource bodySimMain exprSimPrecompiles exprSimHyps
  exprSimSource exprSimCalldataSlice exprSimWordArgs builtinBytes emitHelper
  vyperInterpreter vyperContext vyperState compileEnv exprSimHypsDefs exprLowering exprBopLowering

Theorem code_slice_self_addr_action:
  eval_exprs cx [Builtin st (Env SelfAddr) []] =
    return [AddressV cx.txn.target]
Proof
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM, eval_exprs_nil, return_def] >>
  simp[FUN_EQ_THM, eval_exprs_cons_action, Once evaluate_def,
       builtin_args_length_ok_def, code_slice_source_def,
       precompile_call_success_def, precompile_builtin_def,
       vyperContextTheory.evaluate_builtin_def,
       type_check_def, assert_def, get_accounts_def,
       lift_sum_def, read_result_def, bind_def, ignore_bind_def, return_def]
QED

Theorem code_slice_self_action:
  eval_expr cx
    (Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
      [Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]; start; len]) =
  do sv <- bind (eval_expr cx start) (read_result cx);
     lv <- bind (eval_expr cx len) (read_result cx);
     acc <- get_accounts;
     v <- lift_sum (evaluate_slice (BytesV cx.txn.code) sv lv n);
     return (Value v)
  od
Proof
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM, eval_exprs_nil, return_def] >>
  rewrite_tac[slice_eval_extcode] >>
  simp[code_slice_self_addr_action, eval_exprs_cons_action,
       is_self_addr_def, evaluate_code_source_def, bind_return, bind_assoc] >>
  simp[FUN_EQ_THM, get_accounts_def, lift_sum_def, bind_def, return_def,
       vyperContextTheory.evaluate_builtin_def]
QED

Theorem code_slice_self_compile_decompose:
  compile_slice_code start len sz sa = (r, sb) ==>
  ?out dst sc sd se sf limit.
    r = out /\
    compile_slice_out_buf sz sa = ((out,dst),sc) /\
    emit_op CODESIZE [] sc = (limit,sd) /\
    compile_assert_slice_bounds start len limit sd = ((),se) /\
    emit_void CODECOPY [dst;start;len] se = ((),sf) /\
    emit_void MSTORE [out;len] sf = ((),sb)
Proof
  simp[compile_slice_code_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >>
       simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem code_slice_length_literal:
  slice_operands_ok (Slice n) [Builtin ct (Acc Code) [a]; start; len] ==>
  ?lt j. len = Literal lt (IntL j) /\ 1 <= j /\ j <= &n
Proof
  Cases_on `len` >> simp[vyperTypeSystemTheory.slice_operands_ok_def] >>
  Cases_on `l` >> simp[]
QED

Theorem code_slice_read_length_bound:
  slice_operands_ok (Slice n) [Builtin ct (Acc Code) [a]; start; len] /\
  bind (eval_expr cx len) (read_result cx) es = (INL (IntV (&k)),ee) ==>
  k <= n
Proof
  strip_tac >> drule code_slice_length_literal >> strip_tac >> gvs[] >>
  drule exprSimSliceCapacityReadTheory.slice_literal_read_length >>
  intLib.ARITH_TAC
QED

Theorem code_slice_self_lowering:
  compile_expr cenv ty
    (Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
      [Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]; start; len]) sa = (vv,sb) ==>
  ?sop lop sm sn out.
    lower_value compile_expr cenv ty start sa = (sop,sm) /\
    lower_value compile_expr cenv ty len sm = (lop,sn) /\
    compile_slice_code sop lop (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) sn = (out,sb) /\
    vv = LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out LocMemory)
Proof
  `!bt xs. names_builtin bt xs ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `!xs. ~names_builtin (Slice n) xs` by metis_tac[] >>
  qpat_x_assum `!bt xs. _` kall_tac >>
  simp[compile_expr_builtin_dispatch, compile_builtin_dispatch_component_eq,
       lower_value_child_call, is_self_code_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  Cases_on `compile_slice_code start_op len_op
    (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) st2` >>
  gvs[as_ptr_val_def] >> metis_tac[]
QED

Theorem code_slice_self_operand_pre:
  expr_body_pre cenv cx env
    (Builtin ann (Slice n)
      [Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]; start; len]) es /\
  expr_sim_inv cenv cx env ee ==>
  expr_body_pre cenv cx env start ee /\ expr_body_pre cenv cx env len ee
Proof
  strip_tac >>
  `well_typed_expr env
    (Builtin ann (Slice n)
      [Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]; start; len])` by
    fs[expr_body_pre_def] >>
  drule slice_typed_args >> strip_tac >> gvs[] >>
  `~is_extcode start /\ ~is_extcode len` by
    (fs[vyperTypeSystemTheory.well_typed_expr_def] >>
     conj_tac >> strip_tac >> drule_all well_typed_extcode_type >> simp[]) >>
  conj_tac >> irule expr_body_pre_builtin_arg >>
  qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >> simp[]
QED

Theorem code_slice_self_typing:
  expr_body_pre cenv cx env
    (Builtin ann (Slice n)
      [Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]; start; len]) es ==>
  ann = BaseT (BytesT (Dynamic n)) /\
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  slice_operands_ok (Slice n)
    [Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]; start; len]
Proof
  strip_tac >>
  `well_typed_expr env
    (Builtin ann (Slice n)
      [Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]; start; len])` by
    fs[expr_body_pre_def] >>
  drule slice_typed_args >> strip_tac >> gvs[] >>
  fs[vyperTypeSystemTheory.well_typed_expr_def,
     vyperTypeSystemTheory.well_typed_builtin_app_def,
     vyperTypeSystemTheory.account_item_type_def, vyperASTTheory.expr_type_def]
QED

(* The operand outcome deliberately hides source read traces.  Code slices
   require a literal length, so its compiled operand supplies the same bound. *)
Theorem code_slice_compiled_length_bound:
  slice_operands_ok (Slice n) [Builtin ct (Acc Code) [a]; start; len] /\
  n < dimword (:256) /\ k < dimword (:256) /\
  lower_value compile_expr cenv ty len sa = (lop,sb) /\
  eval_operand lop s = SOME (n2w k) ==>
  k <= n
Proof
  strip_tac >> drule code_slice_length_literal >> strip_tac >> gvs[] >>
  gvs[stmtSimForPartsTheory.lower_value_int_lit, venomStateTheory.eval_operand_def] >>
  `0 <= j /\ j < &dimword (:256)` by intLib.ARITH_TAC >>
  `?q. j = &q` by intLib.COOPER_TAC >> gvs[] >>
  gvs[integer_wordTheory.i2w_def] >> intLib.ARITH_TAC
QED

Theorem code_slice_typed_args_ready_of_body:
  !args tops ctx func cenv cx env arg_ty.
    (!e ee. MEM e args /\ expr_sim_inv cenv cx env ee ==>
      expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)) /\
    body_inv tops ctx cenv cx ==>
    typed_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args
Proof
  Induct >> simp[typed_args_ready_def] >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `expr_body_pre cenv cx env h es /\ is_word_type (expr_type h)` by
        metis_tac[] >>
      rpt conj_tac
      >- metis_tac[body_expr_sim]
      >- first_assum ACCEPT_TAC
      >- metis_tac[expr_body_pre_type_evaluates]
      >- (rpt strip_tac >> drule_all expr_body_pre_stack_result >> simp[]) >>
      rpt strip_tac >> drule_all expr_body_pre_stack_result >> simp[]) >>
  disch_tac >> first_x_assum irule >>
  conj_tac >- metis_tac[] >> qexists_tac `tops` >> simp[]
QED

Theorem code_slice_self_vv_ptr:
  body_inv tops ctx cenv cx /\
  body_exprs_ptr_ok cx [start;len] /\
  expr_body_pre cenv cx env
    (Builtin ann (Slice n)
      [Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]; start; len]) es ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty
    (Builtin ann (Slice n)
      [Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]; start; len]) es
Proof
  strip_tac >> drule code_slice_self_typing >> strip_tac >> gvs[] >>
  `!e ee. MEM e [start;len] /\ expr_sim_inv cenv cx env ee ==>
    expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)` by
    (rpt strip_tac >> drule_all code_slice_self_operand_pre >> strip_tac >>
     fs[is_word_type_def] >> metis_tac[]) >>
  `typed_args_ready ctx func cenv cx (K ty) (expr_sim_inv cenv cx env) [start;len]` by
    (irule code_slice_typed_args_ready_of_body >> conj_tac
     >- first_assum ACCEPT_TAC >> qexists_tac `tops` >> simp[]) >>
  `ptr_args_ready d ctx PG func cenv cx (K ty) (expr_sim_inv cenv cx env) [start;len]` by
    (irule typedWordArgsReadyPtrTheory.body_exprs_ptr_ok_ready >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  rw[expr_vv_sim_ptr_def] >>
  drule code_slice_self_lowering >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es /\ expr_body_pre cenv cx env start es` by
    (fs[expr_body_pre_def] >> metis_tac[]) >>
  `cs_extends sn sb` by
    (qspec_then `sop` (qspec_then `lop` (qspec_then
       `type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))`
       (qspec_then `sn` mp_tac))) externalEntryShapeTheory.compile_slice_code_labels >>
     simp[]) >>
  `cs_extends sa sm /\ cs_extends sm sn` by
    metis_tac[expr_body_pre_lower_value_word_shape, is_word_type_def] >>
  `cs_extends sa sn` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `fn_has_code sa sn func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  rewrite_tac[code_slice_self_action] >>
  ho_match_mp_tac (code_slice_two_uint_outcome_ptr |> Q.INST
    [`arg_ty` |-> `K ty`, `Inv` |-> `expr_sim_inv cenv cx env`, `sb` |-> `sn`]) >>
  simp[] >> suspend "certificates"
QED

Resume code_slice_self_vv_ptr[certificates]:
  conj_tac >- (pure_rewrite_tac[ignore_bind_def, GSYM bind_assoc] >>
    rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >>
    asm_rewrite_tac[ignore_bind_def]) >>
  conj_tac >- (pure_rewrite_tac[ignore_bind_def, GSYM bind_assoc] >>
    rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    asm_rewrite_tac[ignore_bind_def] >>
    goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (pure_rewrite_tac[ignore_bind_def, GSYM bind_assoc] >>
    rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >>
    asm_rewrite_tac[ignore_bind_def]) >>
  conj_tac >- (pure_rewrite_tac[ignore_bind_def, GSYM bind_assoc] >>
    rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    asm_rewrite_tac[ignore_bind_def] >>
    goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (Cases >> simp[oneline exprSimDefsTheory.expr_exit_def]) >>
  rpt gen_tac >> strip_tac >> suspend "continuation"
QED

Resume code_slice_self_vv_ptr[continuation]:
  drule code_slice_self_compile_decompose >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env start es /\ expr_body_pre cenv cx env len es /\
   is_word_type (expr_type start) /\ is_word_type (expr_type len)` by
    (simp[is_word_type_def] >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= sn.cs_next_id /\
   (!x. sop = Var x ==> not_fresh_at sm x) /\ (!x. lop = Var x ==> not_fresh_at sn x)` by
    metis_tac[expr_body_pre_lower_value_word_shape] >>
  `type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) < dimword (:256)` by
    (fs[expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def,
        allocLimitsTheory.type_alloc_ok_def, compileEnvTheory.is_word_type_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `32+n <= type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))` by
    (qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
     simp[compileEnvTheory.type_memory_bytes_def, vfmConstantsTheory.word_size_def]) >>
  `n < dimword (:256)` by decide_tac >>
  `k <= n` by metis_tac[code_slice_compiled_length_bound] >>
  `?p q. out = Var p /\ dst = Var q` by
    (drule exprSimSliceMemoryTheory.slice_out_buf_decompose >> strip_tac >>
     drule bufferAllocationExecutionTheory.compile_alloc_buffer_execution >>
     disch_then (qspec_then `t` strip_assume_tac) >>
     drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
     metis_tac[]) >> gvs[] >>
  `LENGTH cx.txn.code < dimword (:256)` by
    fs[expr_sim_inv_def, vyperTypeInvariantsTheory.context_well_typed_def,
       wordsTheory.dimword_def] >>
  `local_ptrs_reserved cenv sn /\ fn_has_code sn sb func` by
    (conj_tac
     >- (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
         qexists_tac `sa` >> simp[] >>
         decide_tac) >>
     drule_all fragExecTheory.fn_has_code_split >> simp[]) >>
  suspend "runtime"
QED

Resume code_slice_self_vv_ptr[runtime]:
  `i = w2n (n2w i : bytes32) /\ k = w2n (n2w k : bytes32)` by
    (simp[wordsTheory.w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  qpat_x_assum `i = w2n _` (fn th => once_rewrite_tac[th]) >>
  qpat_x_assum `k = w2n _` (fn th => once_rewrite_tac[th]) >>
  irule gasSummaryComposePtrTheory.gas_outcome_ptr_conseq >>
  irule_at Any self_code_continue_outcome_ptr >>
  qpat_assum `compile_slice_out_buf _ sn = _` (irule_at Any) >>
  qpat_assum `emit_op CODESIZE _ _ = _` (irule_at Any) >>
  qpat_assum `compile_assert_slice_bounds _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `emit_void CODECOPY _ _ = _` (irule_at Any) >>
  qpat_assum `emit_void MSTORE _ _ = _` (irule_at Any) >>
  simp[wordsTheory.w2n_n2w] >>
  qexistsl_tac [`Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
    [Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]; start; len]`, `d`, `cenv`] >>
  simp[vyperASTTheory.expr_type_def] >>
  conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  simp[vyperValueTheory.evaluate_type_def, lowered_value_type_def] >>
  conj_tac >- (fs[vyperValueTheory.type_slot_size_def,
    compileEnvTheory.type_memory_bytes_def, vfmConstantsTheory.word_size_def]) >>
  conj_tac >- (
    `LENGTH (TAKE k (DROP i cx.txn.code)) <= n` by
      (simp[listTheory.LENGTH_TAKE_EQ] >> decide_tac) >>
    drule exprSimHypsTheory.word_size_monotone >>
    simp[exprSimPropsTheory.val_store_size_def,
      compileEnvTheory.type_memory_bytes_def, GSYM vfmConstantsTheory.word_size_def]) >>
  simp[vyperASTTheory.expr_type_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id` by decide_tac >>
  drule_all code_slice_vv_post_ptr_rebase >> simp[contextTheory.mk_ptr_def]
QED

Finalise code_slice_self_vv_ptr


(* The value judgment uses the existing unwrap interface, whose inherited
   admission is explicitly authorized by the task's integration plan. *)
Theorem body_code_slice_self_ptr:
  !cx ty n ct st start len.
    body_exprs_ptr_ok cx [start; len] ==>
    body_expr_ptr_ok cx (Builtin ty (Slice n)
      [Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]; start; len])
Proof
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[body_expr_ptr_ok_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `expr_vv_sim_ptr d ctx PG func cenv cx ty'
        (Builtin ty (Slice n)
          [Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]; start; len]) es` by
        (metis_tac[code_slice_self_vv_ptr]) >>
      conj_tac >- metis_tac[expr_sim_ptr_of_vv] >>
      first_assum ACCEPT_TAC) >>
  simp[]
QED
