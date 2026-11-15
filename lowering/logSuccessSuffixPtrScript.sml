(* Successful event path: topic hashing followed by data encoding and LOG. *)
Theory logSuccessSuffixPtr
Ancestors
  logDataEmitSuffixPtr logEmitPtr logTopicsRunPtr logEventCodePtr logStoreEncodeRunPtr
  stmtSimLogSuffixActual stmtSimLogTopics logGhostFramePtr stmtFragPtr
  compileEnv context stmtLowering exprLoweringProps emitHelperProps
  fragGasPathPtr bodyPtrDefs venomState list arithmetic words rich_list stmtLoweringMono loweringPosts

Theorem split_log_ops_data_every:
  !xs flags. EVERY P xs ==> EVERY P (SND (split_log_ops xs flags))
Proof
  Induct >- (Cases >> simp[split_log_ops_def]) >>
  qx_gen_tac `arg` >> PairCases_on `arg` >>
  namedCases_on `flags` ["", "flag flags"]
  >- simp[split_log_ops_def] >>
  Cases_on `flag` >> simp[split_log_ops_def] >>
  pairarg_tac >> gvs[] >>
  rename1 `split_log_ops xs rest = (topics,data)` >>
  first_x_assum (qspec_then `rest` mp_tac) >> simp[]
QED

Theorem log_suffix_prefix_path_ptr:
  ce.ce_event_info (nsid_to_string id) = SOME (h,MAP SND xs,flags) /\
  log_eval_view ce args sa xs sm /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  stmt_state_rel H ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  LENGTH flags = LENGTH xs /\ LENGTH (FILTER I flags) <= 3 /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. supported_scalar_type (SND arg) /\
    ?aty tv. supported_scalar_type aty /\
      log_arg_rel ce cx sa sm es s (FST arg,aty) v /\
      evaluate_type (get_tenv cx) aty = SOME tv /\ value_has_type tv v /\
      ptr_val_ok cx aty v (FST arg) G tn s /\
      (is_bytestring_type aty <=> is_bytestring_type (SND arg)) /\
      encode_event_topic aty v = encode_event_topic (SND arg) v) xs vs /\
  LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    (?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
      value_has_type tv v /\ val_wf tv v) /\
    ptr_val_ok cx (SND arg) v (FST arg) G tn s)
    (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs) /\
  encode_indexed_event_topics flags (MAP SND xs) vs = SOME topics /\
  SUM (MAP (type_memory_bytes ce) (log_non_indexed_types flags (MAP SND xs))) < dimword(:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (log_non_indexed_types flags (MAP SND xs))) < dimword(:256) /\
  vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags (MAP SND xs))
    (log_non_indexed_values flags vs) = SOME avs /\
  ghost_inv H d ce cx es G tn s /\ ~ctx_has_dalloca ctx /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  sb.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?u log_st ptr_op len_op off sz HG tm.
    emit_inst LOG
      (Lit (n2w (LENGTH (Lit (n2w h)::ops))) ::
        REVERSE (Lit (n2w h)::ops) ++ [len_op;ptr_op]) [] log_st = ((),sb) /\
    gas_path_ptr D 0 ctx func PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb))) HG tm (OK u) /\
    fresh_vars_wrt limit_st u /\ stmt_state_rel H ctx func ce cx es u /\
    ghost_inv H d ce cx es HG tm u /\ ghost_kept ce es sm G tn s HG tm /\
    inst_extends sm sb /\ ~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
    SUC u.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sm sb) /\
    lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts log_st sb) (DROP u.vs_inst_idx bb.bb_instructions) /\
    eval_operand ptr_op u = SOME off /\ eval_operand len_op u = SOME sz /\
    eval_operands (Lit (n2w h)::ops) u = SOME (n2w h::topics) /\
    LENGTH (Lit (n2w h)::ops) < dimword(:256) /\
    EVERY (\op. op_taint tm op = {}) (ptr_op::len_op::Lit (n2w h)::ops) /\
    (w2n sz <> 0 ==> ?v. ptr_op = Var v /\ ptr_covers HG tm v u (w2n sz)) /\
    (!i. w2n off <= i /\ i < w2n off + w2n sz ==> i NOTIN tm.t_mem) /\
    mem_bytes_at (w2n off) (w2n sz) u.vs_memory =
      enc (Tuple (vyper_to_abi_types (get_tenv cx) (log_non_indexed_types flags (MAP SND xs)))) (ListV avs) /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_requests = s.vs_requests /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_immutables = s.vs_immutables /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==> lookup_var x u = SOME w)
Proof
  strip_tac >>
  `EVERY (supported_scalar_type o SND) xs` by
    (fs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `SUM (MAP (type_memory_bytes ce) data_tys) < dimword(:256)` >>
  `MAP SND (SND (split_log_ops xs flags)) = data_tys` by
    (simp[Abbr `data_tys`] >> metis_tac[split_log_ops_data_types]) >>
  `LIST_REL (\arg v. supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
      value_has_type tv v /\ val_wf tv v)
    (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs)` by
    (qpat_assum `LIST_REL (\arg v. log_arg_rel _ _ _ _ _ _ _ _ /\ _) (SND _) _` mp_tac >>
     match_mp_tac LIST_REL_mono >> simp[]) >>
  `EVERY supported_scalar_type (MAP SND (SND (split_log_ops xs flags)))` by
    (simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     qpat_assum `LIST_REL (\arg v. supported_scalar_type _ /\ _) (SND _) _`
       (mp_then Any mp_tac LIST_REL_MEM_IMP) >> disch_then drule >>
     strip_tac >> fs[]) >>
  `SUM (MAP (type_memory_bytes ce) (MAP SND (SND (split_log_ops xs flags)))) < dimword(:256)` by
    asm_rewrite_tac[] >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`data_ops` |-> `SND (split_log_ops xs flags)`] log_success_suffix_intervals)) >>
  strip_tac >>
  `ghost_kept ce es sm G tn s G tn` by simp[ghost_kept_refl] >>
  `sm.cs_next_var <= sm.cs_next_var` by simp[] >>
  `LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
    ptr_val_ok cx (SND arg) v (FST arg) G tn s)
    (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs)` by
    (qpat_assum `LIST_REL (\arg v. log_arg_rel _ _ _ _ _ _ _ _ /\ _) (SND _) _` mp_tac >>
     match_mp_tac LIST_REL_mono >> simp[]) >>
  drule_all compile_split_log_topics_frame_path_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  suspend "suffix"
QED
Resume log_suffix_prefix_path_ptr[suffix]:
  markerLib.RESUME_TAC >>
  `fresh_vars_wrt limit_st t` by (first_x_assum irule >> simp[] >> decide_tac) >>
  `~t.vs_halted` by
    (qpat_assum `~s.vs_halted` mp_tac >>
     qpat_assum `t with <|vs_vars := _; vs_inst_idx := _|> = s`
      (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  `local_ptrs_reserved ce st` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
   (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p)` by
    metis_tac[not_fresh_at_mono] >>
  `EVERY (\p. (!z. FST p = Var z ==> not_fresh_at st z) /\ (!l. FST p <> Label l)) xs` by
    (fs[EVERY_MEM] >> metis_tac[not_fresh_at_mono]) >>
  drule split_log_ops_data_every >> disch_then (qspec_then `flags` assume_tac) >>
  `LENGTH ops <= 3` by
    (drule compile_log_topic_ops_length >> drule split_log_ops_lengths >> simp[]) >>
  `LIST_REL (\arg v. log_arg_rel ce cx sa st es t arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
      value_has_type tv v /\ val_wf tv v)
    (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs)` by
    fs[LIST_REL_CONJ, SF ETA_ss] >>
  `LIST_REL (\(op,ty) v. ptr_val_ok cx ty v op Gf tnf t)
    (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs)` by
    (qpat_assum `LIST_REL (\arg v. ptr_val_ok _ _ _ _ Gf tnf t) _ _` mp_tac >>
     match_mp_tac LIST_REL_mono >> Cases >> simp[]) >>
  `abi_size_bound ce.ce_struct_fields (TupleT (MAP SND (SND (split_log_ops xs flags)))) < dimword(:256) /\
   vyper_to_abi_list (get_tenv cx) (MAP SND (SND (split_log_ops xs flags)))
     (log_non_indexed_values flags vs) = SOME avs` by asm_rewrite_tac[] >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st sb) (DROP t.vs_inst_idx bb.bb_instructions)` by
    asm_rewrite_tac[] >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`data_ops` |-> `SND (split_log_ops xs flags)`] log_data_emit_prefix_path_ptr)) >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  suspend "post"
QED
Resume log_suffix_prefix_path_ptr[post]:
  markerLib.RESUME_TAC >>
  drule_all gas_path_ptr_then >> disch_tac >>
  `sm.cs_next_id <= st.cs_next_id` by
    (qpat_assum `compile_log_topic_ops _ sm = _` mp_tac >>
     qspecl_then [`FST (split_log_ops xs flags)`,`sm`] mp_tac (cj 2 ci_mono_list_helpers) >>
     simp[ci_mono_def] >> metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas` by
    (qpat_assum `t with <|vs_vars := _; vs_inst_idx := _|> = s`
      (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  `wb_frame ce es es sm s t` by
    (simp[wb_frame_def, exprSimPropsTheory.locals_kept_mem] >> metis_tac[]) >>
  `ghost_kept ce es sm G tn s HG tm` by
    (drule_all (SIMP_RULE bool_ss [] (Q.INST [`es1` |-> `es`] ghost_kept_wb_trans)) >>
     simp[]) >>
  drule log_topics_opcode_shape >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm st) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb)) =
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st sb))` by
    (qpat_assum `emitted_insts sm sb = _` (fn th => once_rewrite_tac[th]) >>
     simp[FILTER_APPEND]) >>
  `t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
   t.vs_requests = s.vs_requests /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_immutables = s.vs_immutables` by
    (qpat_assum `t with <|vs_vars := _; vs_inst_idx := _|> = s`
      (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  qexistsl_tac [`u`,`log_st`,`ptr_op`,`len_op`,`off`,`sz`,`HG`,`tm`] >>
  qpat_x_assum `MAP SND (SND (split_log_ops xs flags)) = data_tys` SUBST_ALL_TAC >>
  full_simp_tac bool_ss [ADD, ADD_0] >>
  simp[LENGTH_APPEND] >> rpt strip_tac >>
  `not_fresh_at st x` by metis_tac[not_fresh_at_mono] >>
  metis_tac[]
QED
Finalise log_suffix_prefix_path_ptr

Theorem log_success_suffix_path_ptr:
  ~cx.txn.is_static /\
  ce.ce_event_info (nsid_to_string id) = SOME (h,MAP SND xs,flags) /\
  log_eval_view ce args sa xs sm /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  stmt_state_rel H ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  LENGTH flags = LENGTH xs /\ LENGTH (FILTER I flags) <= 3 /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
      value_has_type tv v /\ val_wf tv v) xs vs /\
  encode_indexed_event_topics flags (MAP SND xs) vs = SOME topics /\
  SUM (MAP (type_memory_bytes ce) (log_non_indexed_types flags (MAP SND xs))) < dimword(:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (log_non_indexed_types flags (MAP SND xs))) < dimword(:256) /\
  vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags (MAP SND xs))
    (log_non_indexed_values flags vs) = SOME avs /\
  LIST_REL (\arg v. ptr_val_ok cx (SND arg) v (FST arg) G tn s) xs vs /\
  ghost_inv H d ce cx es G tn s /\ ~ctx_has_dalloca ctx /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  sb.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t HG tm.
    gas_path_ptr D 0 ctx func PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb))) HG tm (OK t) /\
    fresh_vars_wrt limit_st t /\
    stmt_state_rel H ctx func ce cx
      (es with logs := es.logs ++ [<|logger := w2w cx.txn.target;
        topics := n2w h::topics; data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
          (log_non_indexed_types flags (MAP SND xs)))) (ListV avs)|>]) t /\
    ghost_inv H d ce cx
      (es with logs := es.logs ++ [<|logger := w2w cx.txn.target;
        topics := n2w h::topics; data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
          (log_non_indexed_types flags (MAP SND xs)))) (ListV avs)|>]) HG tm t /\
    ghost_kept ce es sm G tn s HG tm /\ inst_extends sm sb /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sm sb) /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w)
Proof
  strip_tac >>
  `LIST_REL (\arg v. supported_scalar_type (SND arg) /\
    ?aty tv. supported_scalar_type aty /\
      log_arg_rel ce cx sa sm es s (FST arg,aty) v /\
      evaluate_type (get_tenv cx) aty = SOME tv /\ value_has_type tv v /\
      ptr_val_ok cx aty v (FST arg) G tn s /\
      (is_bytestring_type aty <=> is_bytestring_type (SND arg)) /\
      encode_event_topic aty v = encode_event_topic (SND arg) v) xs vs` by
    (fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
     qpat_x_assum `!n. n < LENGTH _ ==> log_arg_rel _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
     qexistsl_tac [`SND (EL n xs)`,`tv`] >> simp[]) >>
  `LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    (?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
      value_has_type tv v /\ val_wf tv v) /\
    ptr_val_ok cx (SND arg) v (FST arg) G tn s)
    (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs)` by
    (irule split_log_ops_data_rel >>
     fs[LIST_REL_EL_EQN] >> metis_tac[]) >>
  drule_all log_suffix_prefix_path_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all compile_log_emit_path_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all gas_path_ptr_then >> disch_tac >>
  `t.vs_halted = u.vs_halted /\ t.vs_current_bb = u.vs_current_bb /\
   (!x. lookup_var x t = lookup_var x u)` by
    (qpat_x_assum `t with vs_logs := u.vs_logs = u`
       (fn th => once_rewrite_tac[GSYM th]) >> simp[lookup_var_def]) >>
  qexistsl_tac [`t with vs_inst_idx := SUC u.vs_inst_idx`,`HG`,`tm`] >>
  qpat_x_assum `SUC u.vs_inst_idx = _` SUBST_ALL_TAC >>
  qpat_x_assum `mem_bytes_at (w2n off) (w2n sz) u.vs_memory = _` SUBST_ALL_TAC >>
  full_simp_tac bool_ss [ADD_0] >> fs[Excl "enc_def"] >>
  rpt strip_tac >>
  qpat_x_assum `!x w. not_fresh_at sm x /\ _ ==> _`
    (qspecl_then [`x`,`w`] mp_tac) >>
  simp[lookup_var_def] >> fs[lookup_var_def]
QED

val _ = if null (hyp log_success_suffix_path_ptr) then ()
  else raise Fail "log_success_suffix_path_ptr is not closed";
