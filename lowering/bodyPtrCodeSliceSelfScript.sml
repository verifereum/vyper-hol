Theory bodyPtrCodeSliceSelf
Ancestors
  bodyPtrCodeSliceSelfOperands bodyPtrCodeSliceSelfContinue bodyPtrPreds
  exprPtrUnwrap exprSimSliceSelfCode exprSimSliceSource
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
