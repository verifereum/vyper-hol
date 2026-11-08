Theory stmtLogTopicsMemory
Ancestors
  freshWrites stmtLowering stmtSimLogTopics stmtReasonMemory fragExecMem instMemFrontier
  stmtSimLogArgs exprSimHash exprSimDefs supportedTypes vyperTyping vyperValue
  valueEncoding valueEncodingProps exprSimProps stmtReasonMemory moduleLoweringProps context emitHelper emitHelperProps exprLoweringProps venomExecSemantics
  contractABI venomState venomInst words finite_map list rich_list arithmetic compileEnv

Theorem compile_encode_log_topic_bytes_mem_ok:
  compile_encode_log_topic ptr_op T st = (out,en) /\
  (!x. ptr_op = Var x ==> not_fresh_at st x) /\
  eval_operand ptr_op s = SOME (n2w b) /\ mload b s = n2w n /\
  b+32 < dimword (:256) /\ n < dimword (:256) /\
  b+32+n <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  strip_tac >>
  qpat_x_assum `compile_encode_log_topic _ _ _ = _` mp_tac >>
  simp[compile_encode_log_topic_def, emit_op_def, fresh_var_def, fresh_id_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, Once run_inst_seq_mem_ok_cons] >>
  (conj_tac >- (irule below_frontier_no_ranges >> simp[mk_inst_def])) >>
  simp[step_add_eq, eval_operand_def] >>
  `eval_operand ptr_op (update_var (STRING #"%" (toString st.cs_next_var))
     (n2w b + 32w) s) = SOME (n2w b)` by
    (Cases_on `ptr_op` >> gvs[eval_operand_def] >>
     metis_tac[lookup_var_update_not_fresh, LESS_EQ_REFL]) >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_MLOAD, update_var_def,
    w2n_n2w] >>
  fs[update_var_def] >>
  simp[step_mload_eq, mload_def, read_memory_def, w2n_n2w] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_SHA3, eval_operand_def,
    lookup_var_def, update_var_def, FLOOKUP_UPDATE, word_add_n2w, w2n_n2w] >>
  fs[mload_def, read_memory_def, w2n_n2w]
QED

Theorem compile_encode_log_topic_scalar_mem_ok:
  stmt_state_rel ctx func ce cx es s /\
  log_arg_rel ce cx sa sm es s (x,ty) v /\
  supported_scalar_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ (!z. x = Var z ==> not_fresh_at sm z) /\
  compile_encode_log_topic x (is_bytestring_type ty) sm = (op,sb) /\
  (!w n. ~is_word_type ty /\ eval_operand x s = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w + 32 + 32 * ((n+31) DIV 32) <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s
Proof
  strip_tac >> Cases_on `is_bytestring_type ty`
  >- suspend "bytes" >>
  gvs[compile_encode_log_topic_def, comp_return_def, emitted_insts_def,
    run_inst_seq_mem_ok_def]
QED
Resume compile_encode_log_topic_scalar_mem_ok[bytes]:
  drule_all log_bytestring_arg_view >> strip_tac >>
  `~is_word_type ty` by
    (Cases_on `ty` >> fs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     fs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     fs[is_bytestring_type_def, is_word_type_def]) >>
  `expr_val_rel cx ty v x s` by fs[log_arg_rel_def] >>
  drule_all expr_val_rel_memory >> strip_tac >>
  `(?bv. v = BytesV bv /\ LENGTH bv = LENGTH bs) \/
   (?str. v = StringV str /\ LENGTH str = LENGTH bs)` by
    (Cases_on `ty` >> fs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_bytestring_type_def] >>
     Cases_on `v` >>
     gvs[vyperEventTheory.encode_event_topic_def,
       vyperEventTheory.is_event_bytestring_type_def,
       evaluate_type_def, value_has_type_def, val_in_memory_def,
       is_bytestring_type_def, w2n_n2w, AllCaseEqs()] >>
     NO_TAC) >>
  `b+32+32*((LENGTH bs+31) DIV 32) <= s.vs_alloca_next` by
    (qpat_x_assum `!w n. _` (qspecl_then [`n2w b`,`LENGTH bs`] mp_tac) >>
     simp[w2n_n2w] >> metis_tac[]) >>
  `LENGTH bs <= 32*((LENGTH bs+31) DIV 32)` by
    (simp[GSYM contractABITheory.ceil32_def, contractABITheory.le_ceil32]) >>
  irule compile_encode_log_topic_bytes_mem_ok >>
  qexistsl_tac [`b`,`LENGTH bs`,`op`,`x`] >>
  asm_simp_tac (srw_ss()) [GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  (conj_tac >- decide_tac) >>
  qpat_x_assum `compile_encode_log_topic _ _ _ = _` mp_tac >> simp[]
QED
Finalise compile_encode_log_topic_scalar_mem_ok

Theorem log_topic_rounded_frame[local]:
  (t with vs_vars := s.vs_vars) = s /\
  (!z. not_fresh_at sm z ==> lookup_var z t = lookup_var z s) /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  (!w n. ~is_word_type ty /\ eval_operand x s = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w+(32*((n+31) DIV 32)+32) <= s.vs_alloca_next) ==>
  !w n. ~is_word_type ty /\ eval_operand x t = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w+(32*((n+31) DIV 32)+32) <= t.vs_alloca_next
Proof
  strip_tac >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `_ with vs_vars := _ = _`
      (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next`) >> simp[]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `_ with vs_vars := _ = _`
      (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >> simp[]) >>
  `eval_operand x t = eval_operand x s` by
    (Cases_on `x` >> gvs[eval_operand_def]) >>
  metis_tac[]
QED

Theorem compile_log_topic_ops_mem_ok:
  !xs vs sm ops sb s.
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  compile_log_topic_ops (MAP (\p. (FST p,is_bytestring_type (SND p))) xs) sm = (ops,sb) /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
    (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  LIST_REL (\arg v. !w n. ~is_word_type (SND arg) /\
    eval_operand (FST arg) s = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w+(32*((n+31) DIV 32)+32) <= s.vs_alloca_next) xs vs ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s
Proof
  Induct >- (simp[compile_log_topic_ops_def, comp_return_def] >>
    rpt strip_tac >> gvs[emitted_insts_def, run_inst_seq_mem_ok_def]) >>
  rpt gen_tac >> Cases_on `vs` >> simp[compile_log_topic_ops_cons] >>
  strip_tac >> gvs[] >> rename1 `log_arg_rel ce cx sa sm es s arg v` >>
  Cases_on `arg` >> gvs[] >>
  drule compile_encode_log_topic_scalar_mem_ok >> disch_then drule >>
  disch_then (qspecl_then [`tv`,`sm'`,`op`] mp_tac) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [] >>
    qpat_x_assum `!w n. _` mp_tac >>
    simp_tac (srw_ss()) [AC ADD_ASSOC ADD_COMM])) >> strip_tac >>
  drule_all compile_encode_log_topic_scalar_run >> strip_tac >>
  drule_all log_topic_frontier >> strip_tac >>
  suspend "compose"
QED
Resume compile_log_topic_ops_mem_ok[compose]:
  rename1 `run_inst_seq (emitted_insts sm sc) s = OK u` >>
  `stmt_state_rel ctx func ce cx es u` by
    (irule hash_readonly_state_rel >> goal_assum (drule_at Any) >> simp[]) >>
  `local_ptrs_reserved ce sc` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all log_readonly_args >> strip_tac >>
  `EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sc z) /\
     (!l. FST p <> Label l)) xs` by
    (gvs[EVERY_MEM] >> metis_tac[not_fresh_at_mono]) >>
  `LIST_REL (\arg v. !w n. ~is_word_type (SND arg) /\
    eval_operand (FST arg) u = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w+(32*((n+31) DIV 32)+32) <= u.vs_alloca_next) xs t` by
    (qpat_assum `LIST_REL (\arg v. !w n. _) xs t` mp_tac >>
     qpat_assum `EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!l. FST p <> Label l)) xs` mp_tac >>
     simp_tac bool_ss [LIST_REL_EL_EQN, EVERY_EL] >>
     strip_tac >> strip_tac >> simp[] >>
     qx_gen_tac `i` >> strip_tac >>
     match_mp_tac log_topic_rounded_frame >>
     simp[] >>
     (conj_tac >- metis_tac[]) >>
     qpat_x_assum `!n. n < LENGTH xs ==> !w n'. _` (qspec_then `i` mp_tac) >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sc sb) u` by
    (first_x_assum irule >> simp[] >> qexists_tac `t` >> simp[]) >>
  drule log_topic_inst_extends >> strip_tac >>
  drule log_topics_inst_extends >> strip_tac >>
  `emitted_insts sm sb = emitted_insts sm sc ++ emitted_insts sc sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  simp[] >> irule run_inst_seq_mem_ok_append >> simp[]
QED
Finalise compile_log_topic_ops_mem_ok

Theorem compile_split_log_topics_mem_ok:
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  LENGTH flags = LENGTH xs /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,sb) /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
    (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  encode_indexed_event_topics flags (MAP SND xs) vs = SOME topics /\
  LIST_REL (\arg v. !w n. ~is_word_type (SND arg) /\
    eval_operand (FST arg) s = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w+(32*((n+31) DIV 32)+32) <= s.vs_alloca_next) xs vs ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s /\
  !t. run_inst_seq (emitted_insts sm sb) s = OK t ==>
    t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  drule_all split_log_ops_select >> strip_tac >>
  `compile_log_topic_ops
     (MAP (\p. (FST p,is_bytestring_type (SND p)))
       (MAP FST (FILTER SND (ZIP (xs,flags))))) sm = (ops,sb)` by
    gvs[MAP_MAP_o, combinTheory.o_DEF] >>
  `EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
     (!l. FST p <> Label l)) (MAP FST (FILTER SND (ZIP (xs,flags))))` by
    (irule log_indexed_selection_every >> simp[]) >>
  conj_tac
  >- (irule compile_log_topic_ops_mem_ok >>
      goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `compile_log_topic_ops _ _ = _`)) >>
      qexistsl_tac [`sa`,`MAP FST (FILTER SND (ZIP (vs,flags)))`] >>
      simp[] >> conj_tac >> irule log_indexed_selection_rel >> simp[]) >>
  `LENGTH vs = LENGTH xs` by metis_tac[LIST_REL_LENGTH] >>
  drule_all log_indexed_encoding_select >> strip_tac >>
  `LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
     supported_scalar_type (SND arg) /\
     ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v)
     (MAP FST (FILTER SND (ZIP (xs,flags))))
     (MAP FST (FILTER SND (ZIP (vs,flags))))` by
    (irule log_indexed_selection_rel >> simp[]) >>
  qpat_x_assum `encode_indexed_event_topics flags _ _ = SOME topics` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all compile_log_topic_ops_run >> strip_tac >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `_ with vs_vars := _ = _`
    (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next`) >> simp[]
QED
