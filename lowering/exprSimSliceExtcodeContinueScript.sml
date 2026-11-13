(* Zero-source allocation prefix and external address/tail composition. *)
Theory exprSimSliceExtcodeContinue
Ancestors
  loweringStateRelDefs
  exprSimSliceExtcodeEntry exprSimSliceCompose exprSimSliceExtcode
  exprSimSliceBounds exprSimSliceOrdinaryContinue exprSimSource exprSimHyps
  exprSimPrecompiles exprSimWordArgs emitHelperProps fragGasSeqAbort builtinBytes emitHelper
  exprSimSliceExtcodeContext exprSimSliceMemory exprSimHash loweringHalt loweringPosts venomState
  compileEnv context exprLoweringProps fragExec venomInst pair list rich_list

Theorem slice_extcode_out_control:
  compile_slice_out_buf sz sa = ((out,data),sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  simp[compile_slice_out_buf_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND1, mk_inst_def, is_terminator_def]
QED
Theorem slice_extcode_out_run_control:
  compile_slice_out_buf sz sa = ((out,dst),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  u.vs_current_bb = s.vs_current_bb /\ u.vs_halted = s.vs_halted
Proof
  strip_tac >> drule slice_extcode_out_control >> strip_tac >>
  conj_tac
  >- (irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_current_bb`
        run_inst_seq_preserves_field)) >>
      goal_assum (drule_at Any) >> rpt strip_tac >>
      `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
        (fs[EVERY_MEM] >> metis_tac[]) >>
      `step_inst 0 ctx i ss1 = OK ss2` by simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
      drule_all venomInstPropsTheory.step_preserves_control_flow >> simp[]) >>
  irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_halted`
    run_inst_seq_preserves_field)) >>
  goal_assum (drule_at Any) >> rpt strip_tac >>
  drule_all venomExecPropsTheory.step_inst_base_OK_preserves_halted >> simp[]
QED

Theorem slice_extcode_tail_control:
  compile_slice_extcode addr sop lop sz sa = (r,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb
Proof
  simp[compile_slice_extcode_def, compile_assert_slice_bounds_def,
       compile_slice_out_buf_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def, DROP_APPEND1]
QED


Theorem slice_extcode_output_outcome_prefix:
  compile_slice_out_buf sz sa = ((out,data),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  gas_outcome F tops (ctx,func) source
    (es,t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) Q R ==>
  gas_outcome F tops (ctx,func) source (es,s) Q R
Proof
  strip_tac >> drule slice_extcode_out_control >> strip_tac >>
  irule slice_capture_outcome_prefix >>
  goal_assum (drule_at Any) >> simp[] >>
  fs[fn_has_code_def, IS_PREFIX_APPEND] >>
  simp[DROP_APPEND1, IS_PREFIX_APPEND, APPEND_ASSOC] >>
  qexistsl_tac [`emitted_insts sa sb`, `t`] >> simp[] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem slice_extcode_zero_code:
  compile_slice_extcode addr start len sz sa = (r,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  simp[compile_slice_extcode_def, compile_assert_slice_bounds_def,
       compile_slice_out_buf_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND1, mk_inst_def, is_terminator_def]
QED

Theorem slice_extcode_range_path:
  compile_slice_extcode addr start len sz sa = (r,sb) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand addr s = SOME a /\ eval_operand start s = SOME b /\
  eval_operand len s = SOME n /\
  (!x. MEM (Var x) [addr;start;len] ==> not_fresh_at sa x) /\
  LENGTH (lookup_account (w2w a) s.vs_accounts).code < dimword (:256) /\
  LENGTH (lookup_account (w2w a) s.vs_accounts).code < w2n b + w2n n ==>
  ?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t)
Proof
  strip_tac >>
  `?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t` by
    (drule slice_extcode_shape >> strip_tac >>
     drule_all slice_extcode_prefix_run >> asm_rewrite_tac[] >> strip_tac >>
     qexists_tac `u` >>
     qpat_assum `emitted_insts sa sb = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `emitted_insts sa sd = _` (fn th => rewrite_tac[th]) >>
     qspecl_then [`emitted_insts sa sc ++ emitted_insts sc sd`,
       `emitted_insts sd se ++ emitted_insts se sb`, `s`] mp_tac
       run_inst_seq_append_err >>
     simp[]) >>
  `EVERY (\inst. inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
      ~is_terminator inst.inst_opcode) (emitted_insts sa sb)` by
    (drule slice_extcode_zero_code >> simp[EVERY_MEM]) >>
  drule_all fragGasSeqAbortTheory.run_inst_seq_abort_zero_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> metis_tac[]
QED

Theorem slice_address_read_post:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT AddressT /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  expr_post ctx func cenv cx e es sa sb s ee v op t ==>
  expr_sim_inv cenv cx env ee /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  ?bs. v = BytesV bs /\ LENGTH bs = 20 /\
    eval_operand op t = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `expr_sim_inv cenv cx env ee /\ expr_result_typed env e (Value v)` by
    metis_tac[expr_body_pre_eval] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `value_runtime_typed env (BaseT AddressT) v` by
    gvs[vyperTypeExprResultTheory.expr_result_typed_def,
        vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
        vyperTypeInvariantsTheory.value_result_typed_def,
        vyperTypeExprSoundnessTheory.value_runtime_typed_def,
        vyperValueTheory.evaluate_type_def] >>
  qpat_x_assum `value_runtime_typed _ _ _` mp_tac >>
  simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def,
       vyperValueTheory.evaluate_type_def, vyperTypingTheory.value_has_type_def,
       AllCaseEqs()] >> strip_tac >>
  gvs[] >> Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  irule expr_post_typed_stack_operand >> goal_assum (drule_at Any) >>
  simp[is_word_type_def, vyperValueTheory.evaluate_type_def]
QED

Theorem slice_address_read_outcome:
  expr_type addr = BaseT AddressT /\ expr_body_pre cenv cx env addr es /\
  expr_sim_case nocalls ctx func cenv cx addr /\
  (nocalls ==> int_calls_expr addr = []) /\
  lower_value compile_expr cenv ty addr sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!ee t bs gs.
    bind (eval_expr cx addr) (read_result cx) (es with gas_obs := gs) =
      (INL (BytesV bs),ee) /\
    expr_post ctx func cenv cx addr es sa sb s ee (BytesV bs) op t /\
    expr_sim_inv cenv cx env ee /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    LENGTH bs = 20 /\ ~t.vs_halted /\ ee.gas_obs = [] /\
    eval_operand op t = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (finish_slice (BytesV bs) : evaluation_state -> eval_result evaluation_result)
      (ee,t) Q (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx addr) (read_result cx)) finish_slice) (es,s)
    Q (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `expr_sim ctx func cenv cx ty addr es` by
    (irule expr_sim_case_apply >> simp[] >>
     conj_tac >- (qexists_tac `env` >> fs[]) >>
     qexists_tac `nocalls` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx addr) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  irule slice_read_outcome_bind >> simp[] >>
  qexistsl_tac [`cenv`, `op`, `sa`, `sb`, `ty`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `~t.vs_halted` by metis_tac[slice_marked_read_ok_not_halted] >>
  `?gs. bind (eval_expr cx addr) (read_result cx) (es with gas_obs := gs) =
    (INL v,mid with gas_obs := [])` by
    (fs[gasSummaryTheory.gas_marked_exec_def] >> metis_tac[]) >>
  drule_all slice_address_read_post >> strip_tac >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `gs` >> simp[]
QED

(* The accounts read is deliberately at the state after address evaluation. *)
Theorem slice_extcode_source_tail:
  (do code_acc <- get_accounts;
      code_v <- lift_sum (evaluate_builtin cx code_acc ct (Acc Code) [aty] [BytesV bs]);
      slice_acc <- get_accounts;
      v <- lift_sum (evaluate_builtin cx slice_acc rt (Slice n) tys
          [code_v;IntV (&i);IntV (&k)]);
      return (Value v) od) =
  (do acc <- get_accounts;
      v <- lift_sum (evaluate_slice
          (BytesV (lookup_account (word_of_bytes_be bs) acc).code)
          (IntV (&i)) (IntV (&k)) n);
      return (Value v) od)
Proof
  simp[FUN_EQ_THM, vyperStateTheory.get_accounts_def, vyperStateTheory.bind_def,
       vyperStateTheory.lift_sum_def, vyperStateTheory.return_def,
       vyperContextTheory.evaluate_builtin_def, vyperContextTheory.evaluate_account_op_def]
QED

Theorem slice_extcode_range_outcome:
  gas_marked_path F ctx func s 0 (Abort Revert_abort t) /\
  LENGTH (lookup_account (word_of_bytes_be bs) es.accounts).code < i+k ==>
  gas_outcome F tops (ctx,func)
    (do acc <- get_accounts;
        v <- lift_sum (evaluate_slice
          (BytesV (lookup_account (word_of_bytes_be bs) acc).code)
          (IntV (&i)) (IntV (&k)) n);
        return (Value v) od) (es,s) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >> rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "evaluate_slice range"))`,
               `es`, `Abort Revert_abort t`] >>
  simp[gasSummaryTheory.gas_marked_exec_def,
       vyperStateTheory.get_accounts_def, vyperStateTheory.bind_def,
       vyperStateTheory.lift_sum_def, vyperStateTheory.return_def,
       exprSimSliceSourceTheory.slice_bytes_nat,
       vyperStateTheory.raise_def, exit_result_def, exprSimDefsTheory.expr_exit_def]
QED

Theorem slice_extcode_success_outcome:
  gas_marked_path F ctx func s 0 (OK t) /\
  i+k <= LENGTH (lookup_account (word_of_bytes_be bs) es.accounts).code /\ k <= n /\
  vv_post ctx func cenv cx e es sbase sb s (es with gas_obs := [])
    (Value (BytesV (TAKE k (DROP i
      (lookup_account (word_of_bytes_be bs) es.accounts).code))))
    (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  gas_outcome F tops (ctx,func)
    (do acc <- get_accounts;
        v <- lift_sum (evaluate_slice
          (BytesV (lookup_account (word_of_bytes_be bs) acc).code)
          (IntV (&i)) (IntV (&k)) n);
        return (Value v) od) (es,s)
    (\res ee t. ?tv. res = INL tv /\
       vv_post ctx func cenv cx e es sbase sb s ee tv
         (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t /\
       t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INL (Value (BytesV (TAKE k (DROP i
    (lookup_account (word_of_bytes_be bs) es.accounts).code))))`, `es`, `OK t`] >>
  simp[gasSummaryTheory.gas_marked_exec_def,
       vyperStateTheory.get_accounts_def, vyperStateTheory.bind_def,
       vyperStateTheory.lift_sum_def, vyperStateTheory.return_def,
       exprSimSliceSourceTheory.slice_bytes_nat]
QED

(* The whole extcode slice after its operands: EXTCODESIZE and the bounds
   check, then the output buffer, then the copy into it. *)
Theorem slice_extcode_run_vv_post:
  compile_slice_extcode addr start len sz sa = (r,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  eval_operand addr s = SOME a /\ eval_operand start s = SOME b /\
  eval_operand len s = SOME n /\
  (!x. MEM (Var x) [addr;start;len] ==> not_fresh_at sa x) /\
  LENGTH (lookup_account (w2w a) s.vs_accounts).code < dimword (:256) /\
  32 + w2n n <= sz /\ sz < dimword (:256) /\
  expr_type e = BaseT (BytesT (Dynamic max_len)) /\ w2n n <= max_len ==>
  if LENGTH (lookup_account (w2w a) s.vs_accounts).code < w2n b + w2n n then
    ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
  else
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      !k. vv_post ctx func cenv cx e es sa sb s es
        (Value (BytesV (TAKE (w2n n) (DROP (w2n b)
          (lookup_account (w2w a) s.vs_accounts).code))))
        (LocatedValue (expr_type e) (mk_ptr r LocMemory)) (t with vs_inst_idx := k)
Proof
  strip_tac >> drule slice_extcode_shape >> strip_tac >>
  drule_all slice_extcode_prefix_run >>
  qpat_assum `emitted_insts sa sd = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_assum `emitted_insts sa sb = _` (fn th => rewrite_tac[th]) >>
  Cases_on `LENGTH (lookup_account (w2w a) s.vs_accounts).code < w2n b + w2n n` >>
  asm_rewrite_tac[] >> strip_tac
  >- (qexists_tac `u` >>
      qspecl_then [`emitted_insts sa sd`,
        `emitted_insts sd se ++ emitted_insts se sb`, `s`] mp_tac
        run_inst_seq_append_err >>
      simp[]) >>
  suspend "ok"
QED

Resume slice_extcode_run_vv_post[ok]:
  `u.vs_accounts = s.vs_accounts /\ u.vs_labels = s.vs_labels /\
   u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by
    (qpat_assum `u = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es u` by
    (qpat_assum `u = s with vs_vars := _` SUBST1_TAC >>
     irule exprSimPropsTheory.stmt_state_rel_vars_frame >> simp[] >>
     rpt strip_tac >> fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
  qpat_x_assum `u = s with vs_vars := _` kall_tac >>
  `wb_frame cenv es es sa s u` by
    (match_mp_tac (Q.SPECL [`cenv`,`es`,`es`,`sa`,`s`,`s`,`sa`,`u`]
       exprSimWordArgsTheory.wb_frame_readonly_tail) >>
     simp[exprSimWordArgsTheory.wb_frame_refl] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sd x /\ not_fresh_at se x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se` by
    (conj_tac >> irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `MEM (mk_inst sd.cs_next_id ALLOCA [Lit (n2w sz)]
     [STRING #"%" (toString sd.cs_next_var)]) (fn_insts func)` by
    (irule hash_emitted_inst_mem >> qexistsl_tac [`sa`, `sb`] >>
     asm_rewrite_tac[MEM_APPEND, MEM]) >>
  mp_tac (Q.INST [`s` |-> `u`, `sa` |-> `sd`, `sb` |-> `se`, `out` |-> `r`,
                  `data` |-> `dst`] slice_out_buf_run) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sd se) u = OK t1` >>
  `t1.vs_accounts = s.vs_accounts` by
    (`t1.vs_accounts = u.vs_accounts` suffices_by simp[] >>
     irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_accounts`
       run_inst_seq_preserves_field)) >>
     qexists_tac `emitted_insts sd se` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `emitted_insts sd se = _` (fn th => rewrite_tac[th]) >>
     rw[]
     >- (qspecl_then [`sd.cs_next_id`, `n2w sz`,
           `STRING #"%" (toString sd.cs_next_var)`, `ss1`] strip_assume_tac
           step_alloca_frame >> gvs[]) >>
     gvs[venomExecSemanticsTheory.step_inst_base_opcode_eqs, mk_inst_def,
         venomExecSemanticsTheory.exec_pure2_def, AllCaseEqs(), update_var_def]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
     eval_operand op t1 = eval_operand op s` by
    (Cases >> simp[eval_operand_def] >> rpt strip_tac >> metis_tac[]) >>
  `eval_operand addr t1 = eval_operand addr s /\
   eval_operand start t1 = eval_operand start s /\
   eval_operand len t1 = eval_operand len s` by
    (rpt conj_tac >> first_assum irule >> rpt strip_tac >> gvs[] >>
     metis_tac[MEM]) >>
  `!x. MEM (Var x) [addr;start;len;r;dst] ==> not_fresh_at se x` by
    (rpt strip_tac >> gvs[MEM] >> metis_tac[]) >>
  `w2n b + w2n n <= LENGTH (lookup_account (w2w a) t1.vs_accounts).code` by
    simp[] >>
  `!j off len. FLOOKUP t1.vs_allocas j = SOME (off,len) /\ j < sa.cs_next_id ==>
     regions_disjoint (w2n p) sz off len` by
    (rpt strip_tac >>
     `sd.cs_next_id <> j` by decide_tac >>
     qpat_x_assum `FLOOKUP t1.vs_allocas j = _` mp_tac >>
     qpat_x_assum `FLOOKUP t1.vs_allocas sd.cs_next_id = _` mp_tac >>
     qpat_x_assum `stmt_state_rel _ _ _ _ _ t1` mp_tac >>
     qpat_x_assum `sd.cs_next_id <> j` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[state_allocations_disjoint]) >>
  `(mk_inst sd.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sd.cs_next_var)]).inst_opcode = ALLOCA /\
   (mk_inst sd.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sd.cs_next_var)]).inst_id = sd.cs_next_id` by
    simp[mk_inst_def] >>
  mp_tac (Q.INST [`s` |-> `t1`, `sa` |-> `se`, `sm` |-> `sf`, `out` |-> `r`,
    `sbase` |-> `sa`, `aid` |-> `sd.cs_next_id`, `cap` |-> `sz`,
    `inst` |-> `mk_inst sd.cs_next_id ALLOCA [Lit (n2w sz)]
                  [STRING #"%" (toString sd.cs_next_var)]`]
    slice_extcode_tail_vv_post) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> simp[]) >>
  strip_tac >>
  `wb_frame cenv es es sa s t1` by
    (match_mp_tac (Q.SPECL [`func`,`cenv`,`cx`,`es`,`s`,`sa`,`es`,`es`,`sd`,
       `u`,`t1`,`ctx`] exprSimWordArgsTheory.wb_frame_trans) >> simp[]) >>
  `pure_frame cenv func es sa s t1` by simp[pure_frame_def] >>
  qpat_x_assum `!k. vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `t1.vs_accounts = s.vs_accounts` (fn th => rewrite_tac[th]) >>
  strip_tac >>
  `run_inst_seq ((emitted_insts sa sc ++ emitted_insts sc sd) ++
     (emitted_insts sd se ++ emitted_insts se sb)) s = OK t` by
    (qpat_assum `run_inst_seq (_ ++ _) s = OK u`
       (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
     qpat_assum `run_inst_seq (emitted_insts sd se) u = OK t1`
       (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
     first_assum ACCEPT_TAC) >>
  qexists_tac `t` >> conj_tac
  >- (qpat_x_assum `run_inst_seq ((_ ++ _) ++ _) s = OK t` mp_tac >>
      qpat_assum `emitted_insts sd se = _` (fn th => rewrite_tac[th]) >>
      qpat_assum `sd.cs_next_id = _` (fn th => rewrite_tac[th]) >>
      qpat_assum `sd.cs_next_var = _` (fn th => rewrite_tac[th]) >>
      rewrite_tac[APPEND_ASSOC]) >>
  qx_gen_tac `kk` >>
  qpat_x_assum `!k. vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `kk` assume_tac) >>
  match_mp_tac (Q.INST [`es1` |-> `es`, `sm` |-> `sa`, `t` |-> `t1`]
    exprSimCalldataSliceTheory.vv_post_prefix_frame) >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ t1 _ _ _ _` mp_tac >>
  simp[]
QED

Finalise slice_extcode_run_vv_post

Theorem slice_extcode_tail_outcome:
  compile_slice_extcode addr sop lop sz sa = (r,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand addr s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  eval_operand sop s = SOME (n2w i) /\ eval_operand lop s = SOME (n2w k) /\
  (!x. MEM (Var x) [addr;sop;lop] ==> not_fresh_at sa x) /\
  accounts_agree cx es.accounts s.vs_accounts /\ accounts_well_typed es.accounts /\
  LENGTH bs = 20 /\ i < dimword (:256) /\ k < dimword (:256) /\ k <= n /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  32+n <= sz /\ sz < dimword (:256) /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\ es.gas_obs = [] ==>
  gas_outcome F tops (ctx,func)
    (do acc <- get_accounts;
        v <- lift_sum (evaluate_slice
          (BytesV (lookup_account (word_of_bytes_be bs) acc).code)
          (IntV (&i)) (IntV (&k)) n);
        return (Value v) od) (es,s)
    (\res ee t. ?tv. res = INL tv /\
       vv_post ctx func cenv cx e es sa sb s ee tv
         (LocatedValue (expr_type e) (mk_ptr r LocMemory)) t /\
       t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  drule_all slice_extcode_account >> strip_tac >>
  `LENGTH (lookup_account (w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)))
      s.vs_accounts).code < dimword (:256)` by
    (simp[wordsTheory.dimword_def] >> decide_tac) >>
  `EVERY (\inst. inst.inst_opcode <> INVOKE /\
      ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> GAS)
      (emitted_insts sa sb)` by metis_tac[slice_extcode_zero_code] >>
  Cases_on `i+k <= LENGTH (lookup_account (word_of_bytes_be bs) es.accounts).code`
  >- suspend "success"
  >> suspend "range"
QED

Resume slice_extcode_tail_outcome[range]:
  `LENGTH (lookup_account (w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)))
      s.vs_accounts).code < w2n (n2w i : bytes32) + w2n (n2w k : bytes32)` by simp[] >>
  drule_all slice_extcode_range_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  irule slice_extcode_range_outcome >> simp[] >> metis_tac[]
QED

Resume slice_extcode_tail_outcome[success]:
  `w2n (n2w i : bytes32) + w2n (n2w k : bytes32) <=
    LENGTH (lookup_account (w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)))
      s.vs_accounts).code` by simp[] >>
  `32 + w2n (n2w k : bytes32) <= sz /\ w2n (n2w k : bytes32) <= n` by simp[] >>
  drule_all slice_extcode_run_vv_post >>
  `~(LENGTH (lookup_account (w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)))
      s.vs_accounts).code < w2n (n2w i : bytes32) + w2n (n2w k : bytes32))` by
    decide_tac >>
  pop_assum (fn th => rewrite_tac[th]) >> strip_tac >>
  `EVERY (\inst. inst.inst_opcode <> INVOKE /\
      ~is_terminator inst.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `FILTER (\inst. inst.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  `ci_mono sa sb` by
    (mp_tac (Q.SPECL [`addr`,`sop`,`lop`,`sz`,`sa`]
      exprSimSliceExtcodeContextTheory.slice_extcode_ci_mono) >> simp[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    metis_tac[slice_extcode_tail_control] >>
  `t.vs_current_bb = sb.cs_current_bb /\
   LENGTH (emitted_insts sa sb) + s.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (drule_all (cj 1 fragExecTheory.exec_block_run_inst_seq) >> simp[]) >>
  drule_all fragGasSeqTheory.tuple_run_inst_seq_gas_path >> strip_tac >>
  qpat_x_assum `!ctx'. gas_path _ _ _ _ _` (qspec_then `ctx` assume_tac) >>
  irule slice_extcode_success_outcome >> simp[] >>
  qexists_tac `t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx` >>
  simp[fragGasModeTheory.gas_marked_path_def] >>
  conj_tac
  >- (qpat_x_assum `gas_path _ _ _ _ _` mp_tac >> simp[]) >>
  `es with gas_obs := [] = es` by
    (qpat_x_assum `es.gas_obs = []` (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  qpat_x_assum `!idx. vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `t.vs_inst_idx` mp_tac) >> simp[]
QED

Finalise slice_extcode_tail_outcome

Theorem slice_extcode_entry_post_rebase:
  wb_frame cenv es es sa s u /\ stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  expr_post ctx func cenv cx a es sb sc u ee av aop t /\
  (~expr_has_effect result ==> ~expr_has_effect a) /\
  (~expr_has_effect result ==> pure_frame cenv func es sa s u) /\
  vv_post ctx func cenv cx result ee sa sd t ef tv vv z ==>
  vv_post ctx func cenv cx result es sa sd s ef tv vv z
Proof
  strip_tac >>
  `wb_frame cenv es ee sb u t` by
    (irule expr_post_frame >> goal_assum (drule_at Any)) >>
  `~expr_has_effect result ==> pure_frame cenv func es sa s t` by
    (strip_tac >>
     qpat_x_assum `~expr_has_effect result ==> ~expr_has_effect a` drule >>
     strip_tac >>
     `pure_frame cenv func es sb u t` by
       (qpat_assum `expr_post _ _ _ _ a _ _ _ _ _ _ _ _`
          (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
        qpat_x_assum `~expr_has_effect a ==> _` irule >>
        first_assum ACCEPT_TAC) >>
     qpat_x_assum `~expr_has_effect result ==> pure_frame _ _ _ _ _ _` drule >>
     strip_tac >>
     match_mp_tac (Q.SPECL [`cenv`, `func`, `es`, `es`, `sa`, `sb`, `s`, `u`, `t`]
                     exprSimPropsTheory.pure_frame_trans) >>
     qpat_assum `wb_frame cenv es es sa s u`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     qpat_assum `wb_frame cenv es ee sb u t`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  `wb_frame cenv es ee sa s t` by
    (match_mp_tac (Q.SPECL [`func`, `cenv`, `cx`, `es`, `s`, `sa`, `es`, `ee`,
                            `sb`, `u`, `t`, `ctx`] wb_frame_trans) >>
     simp[]) >>
  irule exprSimCalldataSliceTheory.vv_post_prefix_frame >>
  simp[] >> qexistsl_tac [`ee`, `sa`, `t`] >> simp[]
QED

Theorem slice_extcode_suffix_context:
  lower_value compile_expr cenv ty a sa = (aop,sb) /\
  compile_slice_extcode aop sop lop sz sb = (r,sc) /\
  fn_has_code sa sc func /\ local_ptrs_reserved cenv sa ==>
  ci_mono sa sb /\ ci_mono sb sc /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\
  local_ptrs_reserved cenv sb
Proof
  strip_tac >>
  `ci_mono sa sb` by metis_tac[compile_expr_grows, ci_mono_def] >>
  `ci_mono sb sc` by
    metis_tac[exprSimSliceExtcodeContextTheory.slice_extcode_ci_mono, SND] >>
  `fn_has_code sa sb func /\ fn_has_code sb sc func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  simp[] >> metis_tac[ci_mono_def, local_ptrs_reserved_next_var]
QED

Theorem slice_extcode_continue_entry_seq:
  lower_value compile_expr cenv ty a sa = (aop,sb) /\
  compile_slice_extcode aop sop lop sz sb = (r,sc) /\
  fn_has_code sa sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  expr_type a = BaseT AddressT /\ expr_body_pre cenv cx env a es /\
  expr_sim_case nocalls ctx func cenv cx a /\
  (nocalls ==> int_calls_expr a = []) /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand sop s = SOME (n2w i) /\ eval_operand lop s = SOME (n2w k) /\
  (!op. MEM op [sop;lop] ==>
    (?w. op = Lit w) \/ (?x. op = Var x /\ not_fresh_at sa x)) /\
  (!x. aop = Var x ==> not_fresh_at sb x) /\
  i < dimword (:256) /\ k < dimword (:256) /\ k <= n /\
  32+n <= sz /\ sz < dimword (:256) /\
  (~expr_has_effect result ==> ~expr_has_effect a) /\
  expr_type result = BaseT (BytesT (Dynamic n)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do av <- bind (eval_expr cx a) (read_result cx);
        code_acc <- get_accounts;
        code_v <- lift_sum (evaluate_builtin cx code_acc ct (Acc Code) [expr_type a] [av]);
        slice_acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx slice_acc (expr_type result) (Slice n)
                      tys [code_v;IntV (&i);IntV (&k)]);
        return (Value v) od) (es,s)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx result es sa sc s ee tv
        (LocatedValue (expr_type result) (mk_ptr r LocMemory)) t /\
      t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule_all slice_extcode_suffix_context >> strip_tac >>
  irule slice_address_read_outcome >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >> qexistsl_tac [`cenv`, `env`, `nocalls`, `aop`, `sa`, `sb`, `ty`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx ee t` by fs[loweringPostsTheory.expr_post_def] >>
  `!op. MEM op [sop;lop] ==> eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `(?w. op = Lit w) \/ (?z. op = Var z /\ not_fresh_at sa z)` by metis_tac[] >>
     gvs[venomStateTheory.eval_operand_def] >>
     fs[loweringPostsTheory.expr_post_def, venomStateTheory.lookup_var_def]) >>
  rewrite_tac[slice_extcode_source_tail] >> suspend "tail"
QED

Resume slice_extcode_continue_entry_seq[tail]:
  irule slice_gas_outcome_conseq >>
  qexists_tac `(\res ef z. ?tv. res = INL tv /\
    vv_post ctx func cenv cx result ee sb sc t ef tv
      (LocatedValue (expr_type result) (mk_ptr r LocMemory)) z /\
    z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts)` >>
  qexists_tac `(\res ef r. expr_exit res r)` >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "rebase" >>
  `accounts_well_typed ee.accounts` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_def, vyperTypeInvariantsTheory.state_well_typed_def] >>
  `accounts_agree cx ee.accounts t.vs_accounts` by
    fs[stmt_state_rel_def, state_rel_def, accounts_rel_def] >>
  `?bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sb sc) (DROP (LENGTH sb.cs_current_insts) bb.bb_instructions)` by
    (drule slice_extcode_tail_control >> strip_tac >>
     qpat_x_assum `fn_has_code sb sc func` mp_tac >>
     simp[fn_has_code_def, IS_PREFIX_APPEND] >> strip_tac >>
     qexists_tac `bb` >> simp[DROP_APPEND1, IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  irule slice_extcode_tail_outcome >>
  qpat_assum `compile_slice_extcode _ _ _ _ _ = _` (irule_at Any) >>
  simp[] >>
  `sa.cs_next_var <= sb.cs_next_var` by fs[ci_mono_def] >>
  rpt strip_tac >> fs[MEM] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono,
    venomStateTheory.operand_distinct, venomStateTheory.operand_11]
QED

Resume slice_extcode_continue_entry_seq[rebase]:
  BETA_TAC >> rpt strip_tac >> gvs[] >>
  `wb_frame cenv es ee sa s t` by
    (irule expr_post_frame >> goal_assum (drule_at Any)) >>
  match_mp_tac (Q.INST [`es1` |-> `ee`, `sm` |-> `sb`, `sb` |-> `sc`]
    exprSimCalldataSliceTheory.vv_post_prefix_frame) >>
  simp[] >> fs[ci_mono_def] >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
  qpat_x_assum `~expr_has_effect result ==> ~expr_has_effect a` mp_tac >>
  qpat_x_assum `~expr_has_effect a ==> pure_frame _ _ _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >> metis_tac[]
QED

Finalise slice_extcode_continue_entry_seq
