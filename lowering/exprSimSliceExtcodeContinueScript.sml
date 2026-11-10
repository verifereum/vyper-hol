(* Zero-source allocation prefix and external address/tail composition. *)
Theory exprSimSliceExtcodeContinue
Ancestors
  exprSimSliceExtcodeEntry exprSimSliceCompose exprSimSliceExtcode
  exprSimSliceBounds exprSimSliceOrdinaryContinue exprSimSource exprSimHyps
  exprSimPrecompiles exprSimWordArgs emitHelperProps fragGasSeqAbort builtinBytes emitHelper
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
  compile_slice_extcode addr sop lop out dst sa = (r,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb
Proof
  simp[compile_slice_extcode_def, compile_assert_slice_bounds_def,
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
  compile_slice_extcode addr start len out dst sa = (r,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  strip_tac >> drule slice_extcode_shape >> strip_tac >>
  qpat_x_assum `emitted_insts sa sb = _` (fn th => rewrite_tac[th]) >>
  drule (cj 5 slice_bounds_shape) >> strip_tac >>
  imp_res_tac emitHelperPropsTheory.emitted_insts_emit_op >>
  imp_res_tac emitHelperPropsTheory.emitted_insts_emit_void >>
  simp[emitted_insts_def, DROP_APPEND1, DROP_APPEND2,
       mk_inst_def, is_terminator_def]
QED

Theorem slice_extcode_range_path:
  compile_slice_extcode addr start len out dst sa = (r,sb) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand addr s = SOME a /\ eval_operand start s = SOME b /\
  eval_operand len s = SOME n /\ eval_operand out s = SOME p /\
  eval_operand dst s = SOME d /\
  (!x. MEM (Var x) [addr;start;len;out;dst] ==> not_fresh_at sa x) /\
  LENGTH (lookup_account (w2w a) s.vs_accounts).code < dimword (:256) /\
  LENGTH (lookup_account (w2w a) s.vs_accounts).code < w2n b + w2n n ==>
  ?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t)
Proof
  strip_tac >> drule_all slice_extcode_tail_run >> simp[] >> strip_tac >>
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

Theorem slice_extcode_tail_outcome:
  compile_slice_extcode addr sop lop out dst sa = (r,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand addr s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  eval_operand sop s = SOME (n2w i) /\ eval_operand lop s = SOME (n2w k) /\
  eval_operand out s = SOME p /\ eval_operand dst s = SOME (p+32w) /\
  (!x. MEM (Var x) [addr;sop;lop;out;dst] ==> not_fresh_at sa x) /\
  accounts_agree cx es.accounts s.vs_accounts /\ accounts_well_typed es.accounts /\
  LENGTH bs = 20 /\ i < dimword (:256) /\ k < dimword (:256) /\ k <= n /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sbase.cs_next_var <= sa.cs_next_var /\ sbase.cs_next_id <= aid /\
  aid < sa.cs_next_id /\ aid < sb.cs_next_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
  FLOOKUP s.vs_allocas aid = SOME (w2n p,cap) /\
  w2n p + cap < dimword (:256) /\ 32+n <= cap /\
  (!nm off sz. local_region cenv es.scopes s nm off sz ==>
    regions_disjoint (w2n p) cap off sz) /\
  (!j off sz. FLOOKUP s.vs_allocas j = SOME (off,sz) /\ j < sbase.cs_next_id ==>
    regions_disjoint (w2n p) cap off sz) /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\ es.gas_obs = [] ==>
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
  `32 + w2n (n2w k : bytes32) <= cap /\ w2n (n2w k : bytes32) <= n` by simp[] >>
  drule_all slice_extcode_tail_vv_post >> strip_tac >>
  `EVERY (\inst. inst.inst_opcode <> INVOKE /\
      ~is_terminator inst.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `FILTER (\inst. inst.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  `ci_mono sa sb` by
    (mp_tac (Q.SPECL [`addr`,`sop`,`lop`,`out`,`dst`,`sa`]
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
  vv_post ctx func cenv cx result ee sa sd t ef tv vv z ==>
  vv_post ctx func cenv cx result es sa sd s ef tv vv z
Proof
  strip_tac >>
  `wb_frame cenv es ee sb u t` by
    (irule expr_post_frame >> goal_assum (drule_at Any)) >>
  `wb_frame cenv es ee sa s t` by
    (irule wb_frame_trans >> simp[] >> conj_tac
     >- (qexistsl_tac [`es`, `sb`, `u`] >> simp[]) >> metis_tac[]) >>
  irule exprSimCalldataSliceTheory.vv_post_prefix_frame >>
  simp[] >> qexistsl_tac [`ee`, `sa`, `t`] >> simp[]
QED

Theorem slice_extcode_suffix_context:
  compile_slice_out_buf sz sa = ((out,dst),sb) /\
  lower_value compile_expr cenv ty a sb = (aop,sc) /\
  compile_slice_extcode aop sop lop out dst sc = (r,sd) /\
  fn_has_code sa sd func /\ local_ptrs_reserved cenv sa ==>
  ci_mono sa sb /\ ci_mono sb sc /\ ci_mono sc sd /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\ fn_has_code sc sd func /\
  local_ptrs_reserved cenv sb /\ local_ptrs_reserved cenv sc
Proof
  strip_tac >>
  `ci_mono sa sb` by metis_tac[ci_mono_compile_slice_out_buf, SND] >>
  `ci_mono sb sc` by metis_tac[compile_expr_grows, ci_mono_def] >>
  `ci_mono sc sd` by metis_tac[exprSimSliceExtcodeContextTheory.slice_extcode_ci_mono, SND] >>
  `cs_extends sb sd` by metis_tac[ci_mono_def, cs_extends_trans] >>
  `fn_has_code sa sb func /\ fn_has_code sb sd func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  `fn_has_code sb sc func /\ fn_has_code sc sd func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  simp[] >> metis_tac[ci_mono_def, local_ptrs_reserved_next_var]
QED

Theorem slice_extcode_continue_entry_seq:
  compile_slice_out_buf sz sa = ((out,dst),sb) /\
  lower_value compile_expr cenv ty a sb = (aop,sc) /\
  compile_slice_extcode aop sop lop out dst sc = (r,sd) /\
  fn_has_code sa sd func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  expr_type a = BaseT AddressT /\ expr_body_pre cenv cx env a es /\
  expr_sim_case nocalls ctx func cenv cx a /\
  (nocalls ==> int_calls_expr a = []) /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand sop s = SOME (n2w i) /\ eval_operand lop s = SOME (n2w k) /\
  (!op. MEM op [sop;lop] ==>
    (?w. op = Lit w) \/ (?x. op = Var x /\ not_fresh_at sa x)) /\
  (!x. aop = Var x ==> not_fresh_at sc x) /\
  i < dimword (:256) /\ k < dimword (:256) /\ k <= n /\
  32+n <= sz /\ sz < dimword (:256) /\
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
      vv_post ctx func cenv cx result es sa sd s ee tv
        (LocatedValue (expr_type result) (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sd.cs_current_bb /\ t.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule_all slice_extcode_suffix_context >> strip_tac >>
  drule_all slice_extcode_output_entry >> strip_tac >>
  drule_all slice_extcode_out_owner_inst >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK u` >>
  drule slice_extcode_out_control >> strip_tac >>
  `EVERY (\inst. inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode)
     (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `u.vs_current_bb = sb.cs_current_bb /\ ~u.vs_halted` by
    (drule_all slice_extcode_out_run_control >> simp[]) >>
  irule slice_extcode_output_outcome_prefix >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`dst`, `out`, `sz`] >> simp[] >>
  irule slice_address_read_outcome >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >> qexistsl_tac [`cenv`, `env`, `nocalls`, `aop`, `sb`, `sc`, `ty`] >>
  `LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by simp[] >>
  qpat_x_assum `sb.cs_current_insts = _` kall_tac >>
  simp[] >> reverse conj_tac
  >- simp[stmt_state_rel_inst_idx] >>
  rpt gen_tac >> strip_tac >>
  `sa.cs_next_id <= sa.cs_next_id` by simp[] >>
  `stmt_state_rel ctx func cenv cx es (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    simp[stmt_state_rel_inst_idx] >>
  `stmt_state_rel ctx func cenv cx ee t /\
   eval_operand out t = SOME p /\ eval_operand dst t = SOME (p+32w) /\
   FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n p,sz) /\
   (!nm off len. local_region cenv ee.scopes t nm off len ==>
     regions_disjoint (w2n p) sz off len) /\
   (!j off len. FLOOKUP t.vs_allocas j = SOME (off,len) /\ j < sa.cs_next_id ==>
     regions_disjoint (w2n p) sz off len)` by
    (irule slice_extcode_output_post >>
     qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> rpt strip_tac >>
     qpat_assum `!name off len. local_region _ _ u name off len ==> _` irule >>
     fs[local_region_def, venomStateTheory.lookup_var_def] >> metis_tac[]) >>
  `!op. MEM op [sop;lop] ==> eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `(?w. op = Lit w) \/ (?z. op = Var z /\ not_fresh_at sa z)` by metis_tac[] >>
     gvs[venomStateTheory.eval_operand_def] >>
     `not_fresh_at sb z` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> fs[ci_mono_def]) >>
     fs[loweringPostsTheory.expr_post_def, venomStateTheory.lookup_var_def]) >>
  rewrite_tac[slice_extcode_source_tail] >> suspend "tail"
QED

Resume slice_extcode_continue_entry_seq[tail]:
  irule slice_gas_outcome_conseq >>
  qexists_tac `(\res ef z. ?tv. res = INL tv /\
    vv_post ctx func cenv cx result ee sa sd t ef tv
      (LocatedValue (expr_type result) (mk_ptr out LocMemory)) z /\
    z.vs_current_bb = sd.cs_current_bb /\ z.vs_inst_idx = LENGTH sd.cs_current_insts)` >>
  qexists_tac `(\res ef r. expr_exit res r)` >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "rebase" >>
  `accounts_well_typed ee.accounts` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_def, vyperTypeInvariantsTheory.state_well_typed_def] >>
  `accounts_agree cx ee.accounts t.vs_accounts` by
    fs[stmt_state_rel_def, state_rel_def, accounts_rel_def] >>
  `?bb. lookup_block sc.cs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sc sd) (DROP (LENGTH sc.cs_current_insts) bb.bb_instructions)` by
    (drule slice_extcode_tail_control >> strip_tac >>
     qpat_x_assum `fn_has_code sc sd func` mp_tac >>
     simp[fn_has_code_def, IS_PREFIX_APPEND] >> strip_tac >>
     qexists_tac `bb` >> simp[DROP_APPEND1, IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  irule slice_extcode_tail_outcome >>
  qpat_assum `compile_slice_extcode _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `FLOOKUP t.vs_allocas _ = _` (irule_at Any) >>
  qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  simp[mk_inst_def] >>
  `sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= sc.cs_next_var /\
   sb.cs_next_id <= sc.cs_next_id /\ sc.cs_next_id <= sd.cs_next_id` by
    fs[ci_mono_def] >>
  simp[] >> conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> fs[MEM] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono,
    ci_mono_def, venomStateTheory.operand_distinct, venomStateTheory.operand_11]
QED

Resume slice_extcode_continue_entry_seq[rebase]:
  BETA_TAC >> rpt strip_tac >> gvs[] >>
  irule slice_extcode_entry_post_rebase >> simp[] >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> fs[ci_mono_def] >>
  fs[loweringPostsTheory.wb_frame_def, venomStateTheory.lookup_var_def]
QED

Finalise slice_extcode_continue_entry_seq
