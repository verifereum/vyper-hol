(* Counted terminal actions for ordinary slice. *)
Theory bodyMemSliceTerminal
Ancestors
  bodyMemSliceData bodyMemSliceResult exprSimSliceTerminal bodyMemTbEmptyMemory exprSimVVFrame
  bodyMemBiSha256Compose
  fragGasMode gasOutcome gasSummary exprSimWordArgs vyperState vyperContext
  exprLoweringProps loweringPosts context list words

Theorem slice_terminal_outcome_mem[local]:
  (!tail. source (es with gas_obs := tail) = (res, es with gas_obs := tail)) /\
  gas_path_mem ctx func s 0 r /\
  ((?t. r = OK t /\ Q res (es with gas_obs := []) t) \/
   (exit_result r /\ R res (es with gas_obs := []) r)) ==>
  gas_outcome T tops (ctx,func) source (es,s) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`res`, `es`, `r`] >>
  gvs[gas_marked_exec_def, gas_marked_path_def]
QED

Theorem slice_data_bytes_outcome_mem:
  compile_slice_data sl data sop lop sz sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand sl s = SOME (n2w (LENGTH bs)) /\
  eval_operand data s = SOME (n2w src_base) /\
  eval_operand sop s = SOME (n2w i) /\ eval_operand lop s = SOME (n2w k) /\
  (!op z. MEM op [sl;data;sop;lop] /\ op = Var z ==> not_fresh_at sa z) /\
  mem_bytes_at src_base (LENGTH bs) s.vs_memory = bs /\
  src_base + LENGTH bs <= s.vs_alloca_next /\
  src_base + LENGTH bs < dimword (:256) /\ i < dimword (:256) /\ k < dimword (:256) /\
  32+n <= sz /\ sz < dimword (:256) /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  lowered_value_type cenv e = expr_type e /\
  sz = type_memory_bytes cenv (lowered_value_type cenv e) /\
  slice_operands_ok (Slice n) [src;start;len] /\
  LENGTH bs <= bytelike_type_bound (expr_type src) /\
  bind (eval_expr cx len) (read_result cx) ep = (INL (IntV (&k)),eq) ==>
  gas_outcome T tops (ctx,func)
    (do acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx acc (expr_type e) (Slice n)
               (MAP expr_type [src;start;len]) [BytesV bs;IntV (&i);IntV (&k)]);
        return (Value v) od) (es,s)
    (\res ee t. ?tv. res = INL tv /\
       vv_post ctx func cenv cx e es sa sb s ee tv
         (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t /\
       vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv
         (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t /\
       t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> Cases_on `i+k <= LENGTH bs`
  >- suspend "success"
  >> suspend "range"
QED

Resume slice_data_bytes_outcome_mem[success]:
  `k <= n` by (drule_all exprSimSliceCapacityReadTheory.slice_read_capacity >> simp[]) >>
  `32+k <= sz` by decide_tac >>
  drule_all slice_data_bytes_success_post_mem >> strip_tac >>
  `src_base < dimword (:256) /\ LENGTH bs < dimword (:256)` by decide_tac >>
  `w2n (n2w src_base : bytes32) + w2n (n2w (LENGTH bs) : bytes32) <= s.vs_alloca_next /\
   32 + w2n (n2w k : bytes32) <= sz` by fs[] >>
  drule_all slice_data_success_path_mem >> strip_tac >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (irule sha256_run_inst_seq_alloca_next_mono >>
     qexists_tac `emitted_insts sa sb` >> simp[] >>
     drule slice_data_zero_code >> simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  irule slice_terminal_outcome_mem >>
  qexistsl_tac [`OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`,
    `INL (Value (BytesV (TAKE k (DROP i bs))))`] >>
  simp[get_accounts_def, bind_def, lift_sum_def, return_def, evaluate_builtin_def,
       exprSimSliceSourceTheory.slice_bytes_nat] >>
  qpat_assum `!k'. _ /\ _` (qspec_then `t.vs_inst_idx` strip_assume_tac) >>
  conj_tac
  >- (irule memory_value_post_gas_obs >> simp[mk_ptr_def] >>
      gvs[vv_post_def, mk_ptr_def] >> metis_tac[]) >>
  fs[exprSimMemDefsTheory.vv_store_bound_def, read_result_def, return_def]
QED

Resume slice_data_bytes_outcome_mem[range]:
  `LENGTH bs < dimword (:256)` by decide_tac >>
  `((n2w i + n2w k):bytes32) <+ n2w i \/
    (n2w (LENGTH bs):bytes32) <+ n2w i + n2w k` by
    (fs[dimword_def] >> simp[exprSimSliceBoundsTheory.slice_bounds_word]) >>
  `(!z. sop = Var z ==> not_fresh_at sa z) /\
   (!z. lop = Var z ==> not_fresh_at sa z) /\
   (!z. sl = Var z ==> not_fresh_at sa z)` by (fs[] >> metis_tac[]) >>
  `?t. gas_path_mem ctx func s 0 (Abort Revert_abort t)` by
    (irule slice_data_abort_path_mem >> simp[] >> metis_tac[]) >>
  irule slice_terminal_outcome_mem >>
  qexistsl_tac [`Abort Revert_abort t`,
    `INR (Error (RuntimeError "evaluate_slice range"))`] >>
  simp[get_accounts_def, bind_def, lift_sum_def, return_def, evaluate_builtin_def,
       exprSimSliceSourceTheory.slice_bytes_nat, fragExecTheory.exit_result_def,
       exprSimDefsTheory.expr_exit_def, raise_def]
QED

Finalise slice_data_bytes_outcome_mem

Theorem slice_data_string_outcome_mem:
  compile_slice_data sl data sop lop sz sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand sl s = SOME (n2w (LENGTH text)) /\
  eval_operand data s = SOME (n2w src_base) /\
  eval_operand sop s = SOME (n2w i) /\ eval_operand lop s = SOME (n2w k) /\
  (!op z. MEM op [sl;data;sop;lop] /\ op = Var z ==> not_fresh_at sa z) /\
  mem_bytes_at src_base (LENGTH text) s.vs_memory = MAP (n2w o ORD) text /\
  src_base + LENGTH text <= s.vs_alloca_next /\
  src_base + LENGTH text < dimword (:256) /\ i < dimword (:256) /\ k < dimword (:256) /\
  32+n <= sz /\ sz < dimword (:256) /\
  expr_type e = BaseT (StringT n) /\
  lowered_value_type cenv e = expr_type e /\
  sz = type_memory_bytes cenv (lowered_value_type cenv e) /\
  slice_operands_ok (Slice n) [src;start;len] /\
  LENGTH text <= bytelike_type_bound (expr_type src) /\
  bind (eval_expr cx len) (read_result cx) ep = (INL (IntV (&k)),eq) ==>
  gas_outcome T tops (ctx,func)
    (do acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx acc (expr_type e) (Slice n)
               (MAP expr_type [src;start;len]) [StringV text;IntV (&i);IntV (&k)]);
        return (Value v) od) (es,s)
    (\res ee t. ?tv. res = INL tv /\
       vv_post ctx func cenv cx e es sa sb s ee tv
         (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t /\
       vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv
         (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t /\
       t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> Cases_on `i+k <= LENGTH text`
  >- suspend "success"
  >> suspend "range"
QED

Resume slice_data_string_outcome_mem[success]:
  `k <= n` by (drule_all exprSimSliceCapacityReadTheory.slice_read_capacity >> simp[]) >>
  `32+k <= sz` by decide_tac >>
  drule_all slice_data_string_success_post_mem >> strip_tac >>
  `src_base < dimword (:256) /\ LENGTH text < dimword (:256)` by decide_tac >>
  `w2n (n2w src_base : bytes32) + w2n (n2w (LENGTH text) : bytes32) <= s.vs_alloca_next /\
   32 + w2n (n2w k : bytes32) <= sz` by fs[] >>
  drule_all slice_data_success_path_mem >> strip_tac >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (irule sha256_run_inst_seq_alloca_next_mono >>
     qexists_tac `emitted_insts sa sb` >> simp[] >>
     drule slice_data_zero_code >> simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  irule slice_terminal_outcome_mem >>
  qexistsl_tac [`OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`,
    `INL (Value (StringV (TAKE k (DROP i text))))`] >>
  simp[get_accounts_def, bind_def, lift_sum_def, return_def, evaluate_builtin_def,
       exprSimSliceSourceTheory.slice_string_nat] >>
  qpat_assum `!k'. _ /\ _` (qspec_then `t.vs_inst_idx` strip_assume_tac) >>
  conj_tac
  >- (irule memory_value_post_gas_obs >> simp[mk_ptr_def] >>
      gvs[vv_post_def, mk_ptr_def] >> metis_tac[]) >>
  fs[exprSimMemDefsTheory.vv_store_bound_def, read_result_def, return_def]
QED

Resume slice_data_string_outcome_mem[range]:
  `LENGTH text < dimword (:256)` by decide_tac >>
  `((n2w i + n2w k):bytes32) <+ n2w i \/
    (n2w (LENGTH text):bytes32) <+ n2w i + n2w k` by
    (fs[dimword_def] >> simp[exprSimSliceBoundsTheory.slice_bounds_word]) >>
  `(!z. sop = Var z ==> not_fresh_at sa z) /\
   (!z. lop = Var z ==> not_fresh_at sa z) /\
   (!z. sl = Var z ==> not_fresh_at sa z)` by (fs[] >> metis_tac[]) >>
  `?t. gas_path_mem ctx func s 0 (Abort Revert_abort t)` by
    (irule slice_data_abort_path_mem >> simp[] >> metis_tac[]) >>
  irule slice_terminal_outcome_mem >>
  qexistsl_tac [`Abort Revert_abort t`,
    `INR (Error (RuntimeError "evaluate_slice range"))`] >>
  simp[get_accounts_def, bind_def, lift_sum_def, return_def, evaluate_builtin_def,
       exprSimSliceSourceTheory.slice_string_nat, fragExecTheory.exit_result_def,
       exprSimDefsTheory.expr_exit_def, raise_def]
QED

Finalise slice_data_string_outcome_mem
