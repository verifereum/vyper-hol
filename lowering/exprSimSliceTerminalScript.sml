(* The memory-only terminal action of an ordinary slice. *)
Theory exprSimSliceTerminal
Ancestors
  exprSimSliceDataPost exprSimSliceCapacityRead exprSimSliceCompose
  fragGasSeqAbort exprSimSliceData exprSimSliceBounds gasOutcome gasSummary
  vyperState vyperContext exprSimWordArgs list

Theorem slice_data_zero_code:
  compile_slice_data sl src start len sz sa = (out,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS)
    (emitted_insts sa sb)
Proof
  strip_tac >> drule slice_data_decompose >> strip_tac >>
  drule_all slice_data_insts >> strip_tac >>
  qpat_x_assum `emitted_insts sa sb = _` (fn th => rewrite_tac[th]) >>
  drule (cj 5 slice_bounds_shape) >> strip_tac >>
  simp[] >>
  qpat_x_assum `compile_slice_out_buf _ _ = _` mp_tac >>
  simp[builtinBytesTheory.compile_slice_out_buf_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[contextTheory.compile_alloc_buffer_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac emitHelperPropsTheory.emitted_insts_emit_op >>
  imp_res_tac emitHelperPropsTheory.emitted_insts_emit_void >>
  gvs[exprLoweringPropsTheory.emitted_insts_def,
      rich_listTheory.DROP_APPEND1, venomInstTheory.mk_inst_def,
      venomInstTheory.is_terminator_def] >>
  simp[rich_listTheory.DROP_APPEND2, venomInstTheory.is_terminator_def]
QED

Theorem slice_terminal_outcome[local]:
  (!tail. source (es with gas_obs := tail) = (res, es with gas_obs := tail)) /\
  gas_marked_path F ctx func s 0 r /\
  ((?t. r = OK t /\ Q res (es with gas_obs := []) t) \/
   (exit_result r /\ R res (es with gas_obs := []) r)) ==>
  gas_outcome F tops (ctx,func) source (es,s) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`res`, `es`, `r`] >>
  gvs[gas_marked_exec_def]
QED

Theorem slice_data_range_path:
  compile_slice_data sl data sop lop sz sa = (out,sb) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand sl s = SOME (n2w L) /\
  eval_operand sop s = SOME (n2w i) /\ eval_operand lop s = SOME (n2w k) /\
  (!op z. MEM op [sl;data;sop;lop] /\ op = Var z ==> not_fresh_at sa z) /\
  L < dimword (:256) /\ i < dimword (:256) /\ k < dimword (:256) /\
  ~(i+k <= L) ==>
  ?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t)
Proof
  strip_tac >>
  `((n2w i + n2w k):bytes32) <+ n2w i \/
    (n2w L:bytes32) <+ n2w i + n2w k` by
    (fs[wordsTheory.dimword_def] >> simp[slice_bounds_word]) >>
  `!z. sop = Var z ==> not_fresh_at sa z` by fs[] >>
  `!z. lop = Var z ==> not_fresh_at sa z` by fs[] >>
  `!z. sl = Var z ==> not_fresh_at sa z` by fs[] >>
  drule slice_data_abort >>
  disch_then (qspecl_then [`s`, `n2w k`, `n2w L`, `n2w i`] mp_tac) >>
  simp[] >> strip_tac >>
  `EVERY (\inst. inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
      ~is_terminator inst.inst_opcode) (emitted_insts sa sb)` by
    (drule slice_data_zero_code >> simp[EVERY_MEM]) >>
  drule_all run_inst_seq_abort_zero_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> metis_tac[]
QED

Theorem slice_data_bytes_outcome:
  compile_slice_data sl data sop lop sz sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand sl s = SOME (n2w (LENGTH bs)) /\
  eval_operand data s = SOME (n2w src_base) /\
  eval_operand sop s = SOME (n2w i) /\ eval_operand lop s = SOME (n2w k) /\
  (!op z. MEM op [sl;data;sop;lop] /\ op = Var z ==> not_fresh_at sa z) /\
  mem_bytes_at src_base (LENGTH bs) s.vs_memory = bs /\
  src_base + LENGTH bs < dimword (:256) /\ i < dimword (:256) /\ k < dimword (:256) /\
  32+n <= sz /\ sz < dimword (:256) /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  slice_operands_ok (Slice n) [src;start;len] /\
  LENGTH bs <= bytelike_type_bound (expr_type src) /\
  bind (eval_expr cx len) (read_result cx) ep = (INL (IntV (&k)),eq) ==>
  gas_outcome F tops (ctx,func)
    (do acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx acc (expr_type e) (Slice n)
               (MAP expr_type [src;start;len]) [BytesV bs;IntV (&i);IntV (&k)]);
        return (Value v) od) (es,s)
    (\res ee t. ?tv. res = INL tv /\
       vv_post ctx func cenv cx e es sa sb s ee tv
         (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t /\
       t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `EVERY (\inst. inst.inst_opcode <> INVOKE /\
     ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> GAS)
     (emitted_insts sa sb)` by metis_tac[slice_data_zero_code] >>
  Cases_on `i+k <= LENGTH bs`
  >- suspend "success"
  >> suspend "range"
QED

Resume slice_data_bytes_outcome[success]:
  `k <= n` by (drule_all slice_read_capacity >> simp[]) >>
  `32+k <= sz` by decide_tac >>
  drule_all slice_data_bytes_success_post >> strip_tac >>
  `EVERY (\inst. inst.inst_opcode <> INVOKE /\
      ~is_terminator inst.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `FILTER (\inst. inst.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  `t.vs_current_bb = sb.cs_current_bb /\
   LENGTH (emitted_insts sa sb) + s.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (drule slice_data_control >> strip_tac >>
     drule_all (cj 1 fragExecTheory.exec_block_run_inst_seq) >> simp[]) >>
  drule_all fragGasSeqTheory.tuple_run_inst_seq_gas_path >> simp[] >> strip_tac >>
  `LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb) =
   LENGTH sb.cs_current_insts` by decide_tac >>
  qpat_x_assum `!ctx'. gas_path _ _ _ _ _` (qspec_then `ctx` mp_tac) >>
  simp[] >> strip_tac >>
  irule slice_terminal_outcome >>
  qexistsl_tac [`OK (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx)`,
    `INL (Value (BytesV (TAKE k (DROP i bs))))`] >>
  simp[fragGasModeTheory.gas_marked_path_def, get_accounts_def,
       bind_def, lift_sum_def, return_def, evaluate_builtin_def,
       exprSimSliceSourceTheory.slice_bytes_nat] >>
  qpat_x_assum `!idx. vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `t.vs_inst_idx` mp_tac) >>
  `post_value_type cenv e = expr_type e` by
    (irule loweringPostsTheory.post_value_type_bytestring >>
     simp[compileEnvTheory.is_bytestring_type_def]) >>
  pop_assum mp_tac >>
  qpat_x_assum `expr_type e = _` (fn th => rewrite_tac[th] >> mp_tac th) >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[loweringPostsTheory.vv_post_def, contextTheory.mk_ptr_def,
       loweringPostsTheory.vv_holds_def,
       loweringPostsTheory.vv_at_def, loweringPostsTheory.expr_val_at_def,
       read_result_def, return_def] >>
  rpt strip_tac
  >- (first_x_assum irule >> conj_tac >- first_assum ACCEPT_TAC >>
      qexists_tac `aid` >> simp[]) >>
  qpat_x_assum `locals_kept _ _ _ _ _` mp_tac >>
  simp[loweringPostsTheory.locals_kept_def, loweringPostsTheory.popped_kept_def]
QED

Resume slice_data_bytes_outcome[range]:
  `LENGTH bs < dimword (:256)` by decide_tac >>
  drule_all slice_data_range_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  irule slice_terminal_outcome >>
  qexistsl_tac [`Abort Revert_abort t`,
    `INR (Error (RuntimeError "evaluate_slice range"))`] >>
  simp[get_accounts_def, bind_def, lift_sum_def, return_def, evaluate_builtin_def,
       exprSimSliceSourceTheory.slice_bytes_nat, fragExecTheory.exit_result_def,
       exprSimDefsTheory.expr_exit_def, raise_def]
QED

Finalise slice_data_bytes_outcome

Theorem slice_data_string_outcome:
  compile_slice_data sl data sop lop sz sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand sl s = SOME (n2w (LENGTH text)) /\
  eval_operand data s = SOME (n2w src_base) /\
  eval_operand sop s = SOME (n2w i) /\ eval_operand lop s = SOME (n2w k) /\
  (!op z. MEM op [sl;data;sop;lop] /\ op = Var z ==> not_fresh_at sa z) /\
  mem_bytes_at src_base (LENGTH text) s.vs_memory = MAP (n2w o ORD) text /\
  src_base + LENGTH text < dimword (:256) /\ i < dimword (:256) /\ k < dimword (:256) /\
  32+n <= sz /\ sz < dimword (:256) /\
  expr_type e = BaseT (StringT n) /\
  slice_operands_ok (Slice n) [src;start;len] /\
  LENGTH text <= bytelike_type_bound (expr_type src) /\
  bind (eval_expr cx len) (read_result cx) ep = (INL (IntV (&k)),eq) ==>
  gas_outcome F tops (ctx,func)
    (do acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx acc (expr_type e) (Slice n)
               (MAP expr_type [src;start;len]) [StringV text;IntV (&i);IntV (&k)]);
        return (Value v) od) (es,s)
    (\res ee t. ?tv. res = INL tv /\
       vv_post ctx func cenv cx e es sa sb s ee tv
         (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t /\
       t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `EVERY (\inst. inst.inst_opcode <> INVOKE /\
     ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> GAS)
     (emitted_insts sa sb)` by metis_tac[slice_data_zero_code] >>
  Cases_on `i+k <= LENGTH text`
  >- suspend "success"
  >> suspend "range"
QED

Resume slice_data_string_outcome[success]:
  `k <= n` by (drule_all slice_read_capacity >> simp[]) >>
  `32+k <= sz` by decide_tac >>
  drule_all slice_data_string_success_post >> strip_tac >>
  `EVERY (\inst. inst.inst_opcode <> INVOKE /\
      ~is_terminator inst.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `FILTER (\inst. inst.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  `t.vs_current_bb = sb.cs_current_bb /\
   LENGTH (emitted_insts sa sb) + s.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (drule slice_data_control >> strip_tac >>
     drule_all (cj 1 fragExecTheory.exec_block_run_inst_seq) >> simp[]) >>
  drule_all fragGasSeqTheory.tuple_run_inst_seq_gas_path >> simp[] >> strip_tac >>
  `LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb) =
   LENGTH sb.cs_current_insts` by decide_tac >>
  qpat_x_assum `!ctx'. gas_path _ _ _ _ _` (qspec_then `ctx` mp_tac) >>
  simp[] >> strip_tac >>
  irule slice_terminal_outcome >>
  qexistsl_tac [`OK (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx)`,
    `INL (Value (StringV (TAKE k (DROP i text))))`] >>
  simp[fragGasModeTheory.gas_marked_path_def, get_accounts_def,
       bind_def, lift_sum_def, return_def, evaluate_builtin_def,
       exprSimSliceSourceTheory.slice_string_nat] >>
  qpat_x_assum `!idx. vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `t.vs_inst_idx` mp_tac) >>
  `post_value_type cenv e = expr_type e` by
    (irule loweringPostsTheory.post_value_type_bytestring >>
     simp[compileEnvTheory.is_bytestring_type_def]) >>
  pop_assum mp_tac >>
  qpat_x_assum `expr_type e = _` (fn th => rewrite_tac[th] >> mp_tac th) >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[loweringPostsTheory.vv_post_def, contextTheory.mk_ptr_def,
       loweringPostsTheory.vv_holds_def,
       loweringPostsTheory.vv_at_def, loweringPostsTheory.expr_val_at_def,
       read_result_def, return_def] >>
  rpt strip_tac
  >- (first_x_assum irule >> conj_tac >- first_assum ACCEPT_TAC >>
      qexists_tac `aid` >> simp[]) >>
  qpat_x_assum `locals_kept _ _ _ _ _` mp_tac >>
  simp[loweringPostsTheory.locals_kept_def, loweringPostsTheory.popped_kept_def]
QED

Resume slice_data_string_outcome[range]:
  `LENGTH text < dimword (:256)` by decide_tac >>
  drule_all slice_data_range_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  irule slice_terminal_outcome >>
  qexistsl_tac [`Abort Revert_abort t`,
    `INR (Error (RuntimeError "evaluate_slice range"))`] >>
  simp[get_accounts_def, bind_def, lift_sum_def, return_def, evaluate_builtin_def,
       exprSimSliceSourceTheory.slice_string_nat, fragExecTheory.exit_result_def,
       exprSimDefsTheory.expr_exit_def, raise_def]
QED

Finalise slice_data_string_outcome
