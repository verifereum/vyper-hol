(* Successful event path: topic hashing followed by data encoding and LOG. *)
Theory logSuccessSuffixPtr
Ancestors
  logDataEmitSuffixPtr logTopicsRunPtr logEventCodePtr logStoreEncodeRunPtr
  stmtSimLogSuffixActual stmtSimLogTopics logGhostFramePtr stmtFragPtr
  compileEnv context stmtLowering exprLoweringProps emitHelperProps
  fragGasPathPtr bodyPtrDefs list arithmetic words rich_list stmtLoweringMono loweringPosts

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

Theorem log_success_suffix_path_ptr:
  ce.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_log_eval_all ce args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
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
  ghost_inv d ce cx es G tn s /\ ~ctx_has_dalloca ctx /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  sb.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t H tm.
    gas_path_ptr D 0 ctx func PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb))) H tm (OK t) /\
    fresh_vars_wrt limit_st t /\
    stmt_state_rel ctx func ce cx
      (es with logs := es.logs ++ [<|logger := w2w cx.txn.target;
        topics := n2w h::topics; data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
          (log_non_indexed_types flags (MAP SND xs)))) (ListV avs)|>]) t /\
    ghost_inv d ce cx
      (es with logs := es.logs ++ [<|logger := w2w cx.txn.target;
        topics := n2w h::topics; data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
          (log_non_indexed_types flags (MAP SND xs)))) (ListV avs)|>]) H tm t /\
    ghost_kept ce es sm G tn s H tm /\ inst_extends sm sb /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sm sb) /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w)
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `SUM (MAP (type_memory_bytes ce) data_tys) < dimword(:256)` >>
  `MAP SND (SND (split_log_ops xs flags)) = data_tys` by
    (simp[Abbr `data_tys`] >> metis_tac[split_log_ops_data_types]) >>
  `LIST_REL (\arg v. supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
      value_has_type tv v /\ val_wf tv v) xs vs` by
    (qpat_assum `LIST_REL (\arg v. log_arg_rel _ _ _ _ _ _ _ _ /\ _) xs vs` mp_tac >>
     match_mp_tac LIST_REL_mono >> simp[]) >>
  `LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs` by
    (qpat_assum `LIST_REL (\arg v. log_arg_rel _ _ _ _ _ _ _ _ /\ _) xs vs` mp_tac >>
     match_mp_tac LIST_REL_mono >> simp[] >> metis_tac[]) >>
  qpat_assum `LIST_REL (\arg v. supported_scalar_type _ /\ _) xs vs`
    (mp_then Any mp_tac split_log_ops_data_rel) >>
  disch_then drule >> disch_tac >>
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
  drule_all compile_split_log_topics_path_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  suspend "suffix"
QED
Resume log_success_suffix_path_ptr[suffix]:
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
    (Q.INST [`data_ops` |-> `SND (split_log_ops xs flags)`] log_data_emit_suffix_path_ptr)) >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  suspend "post"
QED
Resume log_success_suffix_path_ptr[post]:
  markerLib.RESUME_TAC >>
  drule_all gas_path_ptr_then >> disch_tac >>
  `sm.cs_next_id <= st.cs_next_id` by
    (qpat_assum `compile_log_topic_ops _ sm = _` mp_tac >>
     qspecl_then [`FST (split_log_ops xs flags)`,`sm`] mp_tac (cj 2 ci_mono_list_helpers) >>
     simp[ci_mono_def] >> metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas` by
    (qpat_assum `t with <|vs_vars := _; vs_inst_idx := _|> = s`
      (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  `wb_frame ce es sm s t` by
    (simp[wb_frame_def, locals_kept_def] >> metis_tac[]) >>
  `ghost_kept ce es sm G tn s H tm` by
    (drule_all (SIMP_RULE bool_ss [] (Q.INST [`es1` |-> `es`] ghost_kept_wb_trans)) >>
     simp[]) >>
  drule log_topics_opcode_shape >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm st) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb)) =
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st sb))` by
    (qpat_assum `emitted_insts sm sb = _` (fn th => once_rewrite_tac[th]) >>
     simp[FILTER_APPEND]) >>
  qexistsl_tac [`t'`,`H`,`tm`] >>
  qpat_x_assum `MAP SND (SND (split_log_ops xs flags)) = data_tys` SUBST_ALL_TAC >>
  full_simp_tac bool_ss [ADD, ADD_0] >>
  simp[LENGTH_APPEND] >> rpt strip_tac >>
  `not_fresh_at st x` by metis_tac[not_fresh_at_mono] >>
  metis_tac[]
QED
Finalise log_success_suffix_path_ptr

val _ = if null (hyp log_success_suffix_path_ptr) then ()
  else raise Fail "log_success_suffix_path_ptr is not closed";
