(* Counted memory execution of the raw_call output allocation and call. *)
Theory rawCallOracleMemory
Ancestors
  rawCallArgumentMemory bodyMemRawCallBounds bodyMemBiMethodIdSuffix
  exprSimRawCall exprSafeOperand fragExec exprLoweringProps fragGasMode entrySinkExtraction builtinSystem context
  emitHelper emitHelperProps compileEnv venomExecSemantics venomState venomInst
  rich_list list

Theorem raw_call_outbuf_no_gas:
  compile_raw_call_outbuf cap sa = ((ov,op),sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Cases_on `0 < cap` >>
  simp[compile_raw_call_outbuf_def, compile_alloc_buffer_def, emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem raw_call_outbuf_counted_mem:
  compile_raw_call_outbuf cap sa = ((ov,op),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  t.vs_current_bb = sb.cs_current_bb /\ s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> drule_all raw_call_outbuf_no_gas >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule raw_call_outbuf_mem_ok >> goal_assum (drule_at Any)) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all method_id_run_path_mem >> simp[gas_marked_path_def] >> strip_tac >>
  drule_all raw_call_outbuf_frontier >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> simp[]
QED

Theorem raw_call_emit_counted_mem:
  emit_op (if stat then STATICCALL else CALL) ops sa = (ok,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_mem_below_frontier
    (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL) ops
      [STRING #"%" (toString sa.cs_next_var)]) s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    metis_tac[emit_op_same_blocks, same_blocks_def] >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by simp[] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (Cases_on `stat` >>
     simp[fragExecMemTheory.run_inst_seq_mem_ok_last,
          memSafeRunTheory.inst_dload_in_section_other, mk_inst_def] >>
     fs[mk_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (Cases_on `stat` >> simp[mk_inst_def, is_terminator_def]) >>
  drule_all method_id_run_path_mem >> simp[gas_marked_path_def] >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> simp[]
QED

Theorem raw_call_outbuf_run_mem:
  compile_raw_call_outbuf cap sa = ((ov,op),sb) /\
  (0 < cap ==> ((cap+31) DIV 32)*32+32 < dimword (:256)) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sa s t /\
    t.vs_memory = s.vs_memory /\ eval_operand ov t = SOME w /\
    eval_operand op t = SOME (if cap = 0 then w else w+32w) /\
    FLOOKUP t.vs_allocas sa.cs_next_id =
      SOME (w2n w, if cap = 0 then 0 else ((cap+31) DIV 32)*32+32) /\
    w2n w + (if cap = 0 then 0 else ((cap+31) DIV 32)*32+32) < dimword (:256) /\
    (0 < cap ==> w2n (w+32w) = w2n w+32) /\
    (!name b sz. local_region cenv es.scopes t name b sz ==>
      regions_disjoint (w2n w) (if cap=0 then 0 else ((cap+31) DIV 32)*32+32) b sz) /\
    (cenv.ce_is_ctor ==> !name tv v off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
      regions_disjoint off (type_memory_size tv) (w2n w)
        (if cap=0 then 0 else ((cap+31) DIV 32)*32+32)) /\
    (!x. ov = Var x \/ op = Var x ==> not_fresh_at sb x) /\
    gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    t.vs_current_bb = sb.cs_current_bb /\ s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> `alloca_inv s` by fs[stmt_state_rel_def] >>
  Cases_on `cap = 0`
  >- (gvs[] >> drule_all raw_call_outbuf_zero_run >> strip_tac >>
      drule_all raw_call_outbuf_counted_mem >> strip_tac >>
      qexistsl_tac [`t`,`w`] >> simp[] >> metis_tac[]) >>
  `0 < cap` by decide_tac >>
  `(cap+31) DIV 32 * 32 + 32 < dimword (:256)` by simp[] >>
  drule_all raw_call_outbuf_positive_run >> strip_tac >>
  drule_all raw_call_outbuf_counted_mem >> strip_tac >>
  qexistsl_tac [`t`,`w`] >> fs[arithmeticTheory.MULT_COMM] >> metis_tac[]
QED

Theorem raw_call_oracle_run_mem:
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]) sa = (ok,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME ro /\ eval_operand val_op s = SOME val_word /\
  w2w aw = target /\
  w2n (if stat then 0w else val_word) = (case value_opt of NONE => 0 | SOME n => n) /\
  stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\ cap < dimword (:256) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    b + sz <= w2n ro \/ w2n ro + cap <= b) /\
  (cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    off + type_memory_size tv <= w2n ro \/ w2n ro + cap <= off) /\
  (w2n az = 0 \/ w2n ao + w2n az <= s.vs_alloca_next) /\
  (cap = 0 \/ w2n ro + cap <= s.vs_alloca_next) /\
  wb_frame cenv initial_es initial s0 s /\ initial.cs_next_var <= sa.cs_next_var /\
  (!aid b sz. aid < initial.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n ro) cap b sz) /\
  (!name b sz. local_region cenv initial_es.scopes s0 name b sz ==>
    regions_disjoint (w2n ro) cap b sz) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    u = update_var (STRING #"%" (toString sa.cs_next_var))
      (bool_to_word outcome.co_success) t /\
    eval_operand ok u = SOME (bool_to_word outcome.co_success) /\
    stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
    t = s with <| vs_outcomes := t.vs_outcomes; vs_requests := t.vs_requests;
      vs_accounts := t.vs_accounts; vs_transient := t.vs_transient;
      vs_logs := t.vs_logs; vs_pending_deletions := t.vs_pending_deletions;
      vs_returndata := t.vs_returndata; vs_memory := t.vs_memory |> /\
    t.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE cap outcome.co_returnData) s).vs_memory /\
    t.vs_returndata = outcome.co_returnData /\
    mem_bytes_at (w2n ro) (LENGTH (TAKE cap outcome.co_returnData)) t.vs_memory =
      TAKE cap outcome.co_returnData /\
    gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    u.vs_current_bb = sb.cs_current_bb /\
    wb_frame cenv initial_es initial s0 u /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_fmp = s.vs_fmp /\ u.vs_returndata = outcome.co_returnData /\
    ~u.vs_halted /\
    (!p. safe_operand sa p ==> eval_operand p u = eval_operand p s)
Proof
  strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `w2n (n2w cap : bytes32) = cap` by simp[wordsTheory.w2n_n2w] >>
  drule_at (Pat `stmt_state_rel _ _ _ _ _ _`) raw_call_oracle_emit_run_aged >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `take_call_outcome _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`val_word`,`ro`,`gas`,`aw`] mp_tac) >>
  (impl_tac >- (fs[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `t` (qx_choose_then `u` strip_assume_tac)) >>
  `inst_mem_below_frontier
    (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
       else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)])
      [STRING #"%" (toString sa.cs_next_var)]) s` by
    (irule raw_call_input_output_frontier >>
     conj_tac
     >- (qexistsl_tac [`ao`,`az`] >> fs[wordsTheory.w2n_eq_0]) >>
     qexistsl_tac [`ro`,`n2w cap`] >> fs[eval_operand_def]) >>
  drule_all raw_call_emit_counted_mem >> strip_tac >>
  `t.vs_vars = s.vs_vars /\ t.vs_allocas = s.vs_allocas /\
   t.vs_fmp = s.vs_fmp /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_halted = s.vs_halted` by
    (qpat_assum `t = s with <| vs_outcomes := _; vs_requests := _;
       vs_accounts := _; vs_transient := _; vs_logs := _;
       vs_pending_deletions := _; vs_returndata := _; vs_memory := _ |>`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `~not_fresh_at initial (STRING #"%" (toString sa.cs_next_var))` by
    simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  `wb_frame cenv initial_es initial s0 u` by
    (qpat_assum `u = update_var _ _ t` (fn th => once_rewrite_tac[th]) >>
     irule raw_call_oracle_frame >> simp[] >>
     goal_assum (drule_at (Pat `wb_frame _ _ _ _ _`)) >>
     qexistsl_tac [`w2n ro`, `TAKE cap outcome.co_returnData`] >> simp[] >>
     conj_tac >> rpt gen_tac >> strip_tac >>
     first_x_assum (drule_all_then mp_tac) >>
     simp[regions_disjoint_def, LENGTH_TAKE_EQ] >> decide_tac) >>
  qexistsl_tac [`t`,`u`] >>
  qpat_x_assum `u = update_var _ _ t` SUBST_ALL_TAC >>
  simp[update_var_def] >> gvs[] >> rpt strip_tac >>
  Cases_on `p` >> gvs[safe_operand_def, eval_operand_def, lookup_var_def,
    update_var_def, finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def,
    ASCIInumbersTheory.toString_inj]
QED

