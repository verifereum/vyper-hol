Theory stmtLogDataMemory
Ancestors
  stmtSimLogDataRun stmtSimLogDataFrame stmtSimLogData stmtSimLogTopics
  stmtLogTopicsMemory bodyCopyMemory bodyAllocMemory abiBuiltinAllocation stmtReasonMemory exprSimHash exprSimProps
  exprSimBufferStore exprSimDefs supportedTypes context emitHelperProps
  fragExecMem instMemFrontier valueEncoding words list arithmetic compileEnv exprLoweringProps moduleLoweringProps venomInst venomState freshWrites

Theorem log_scalar_store_mem_ok:
  compile_store_memory ce src dst ty ty sa = ((),sb) /\
  supported_scalar_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\ expr_val_rel cx ty v src s /\
  eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  type_memory_bytes ce ty < dimword (:256) /\
  w2n d + type_memory_bytes ce ty <= s.vs_alloca_next /\
  (!w. ~is_word_type ty /\ eval_operand src s = SOME w ==>
     w2n w + val_store_size tv v <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (gvs[compile_store_memory_def] >>
      drule emitted_insts_emit_void >> strip_tac >>
      simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE] >>
      `type_memory_bytes ce ty = 32` by
        (Cases_on `ty` >> gvs[is_word_type_def, type_memory_bytes_def] >>
         rename1 `BaseT bt` >> Cases_on `bt` >>
         gvs[is_word_type_def, type_memory_bytes_def] >>
         rename1 `BytesT bd` >> Cases_on `bd` >>
         gvs[is_word_type_def, type_memory_bytes_def]) >> simp[]) >>
  `is_bytestring_type ty` by metis_tac[log_scalar_topic_shape] >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    metis_tac[log_scalar_memory_size] >>
  `?w. eval_operand src s = SOME w /\
       val_in_memory tv v (w2n w) s.vs_memory` by
    (fs[loweringPostsTheory.expr_val_rel_def] >> metis_tac[]) >>
  drule_all buffer_typed_bytestring_header >> strip_tac >>
  drule_all val_store_size_le >> strip_tac >>
  gvs[compile_store_memory_def] >>
  irule compile_store_bytestring_body_mem_ok >>
  qexistsl_tac [`d`,`dst`,`len`,`src`,`w`] >> simp[] >>
  metis_tac[]
QED

Theorem compile_log_store_data_mem_ok:
  !xs vs off sa sb s.
  compile_log_store_data ce xs buf off sa = ((),sb) /\
  LIST_REL (log_data_source cx b cap s) xs vs /\
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sa x) xs /\
  (!x. buf = Var x ==> not_fresh_at sa x) /\
  eval_operand buf s = SOME (n2w b) /\
  off + SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= cap /\
  b + cap < dimword (:256) /\ b + cap <= s.vs_alloca_next /\
  LIST_REL (\arg v. !tv w. ~is_word_type (SND arg) /\
    evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
    eval_operand (FST arg) s = SOME w ==>
    w2n w + val_store_size tv v <= s.vs_alloca_next) xs vs ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Induct >- (simp[stmtLoweringTheory.compile_log_store_data_def,
    comp_return_def] >> rpt strip_tac >>
    gvs[emitted_insts_def, run_inst_seq_mem_ok_def]) >>
  rpt gen_tac >> Cases_on `vs` >> simp[] >> strip_tac >>
  Cases_on `h` >> gvs[] >>
  rename1 `log_data_source cx b cap s (src,ty) v` >>
  `supported_scalar_type ty` by fs[log_data_source_def] >>
  drule_all compile_log_store_data_split >> strip_tac >>
  `?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
    value_has_type tv v /\ val_wf tv v /\ expr_val_rel cx ty v src s` by
    fs[log_data_source_def] >>
  drule_all log_data_address_value >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  drule_all log_data_address_shape >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    (drule emitted_insts_emit_op >> strip_tac >>
     simp[run_inst_seq_mem_ok_last, below_frontier_no_ranges, mk_inst_def]) >>
  suspend "field"
QED
Resume compile_log_store_data_mem_ok[field]:
  `u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `_ with vs_vars := _ = _`
      (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next`) >> simp[]) >>
  `u.vs_labels = s.vs_labels` by
    (qpat_assum `_ with vs_vars := _ = _`
      (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >> simp[]) >>
  `eval_operand src u = eval_operand src s` by
    (Cases_on `src` >> gvs[eval_operand_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sn) u` by
    (irule log_scalar_store_mem_ok >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
     qexistsl_tac [`n2w (b+off)`,`v`] >>
     simp[w2n_n2w] >>
     metis_tac[not_fresh_at_mono]) >>
  `b + off < dimword (:256) /\ type_memory_bytes ce ty < dimword (:256)` by
    decide_tac >>
  drule_all log_data_field_run >> strip_tac >>
  suspend "tail"
QED
Resume compile_log_store_data_mem_ok[tail]:
  `type_memory_bytes ce ty = type_memory_size tv` by
    metis_tac[log_scalar_memory_size] >>
  `log_write_frame sa (b+off) (type_memory_bytes ce ty) s q` by
    (simp[log_write_frame_def] >> metis_tac[ADD_ASSOC]) >>
  `log_write_frame sa b cap s q` by
    (irule log_write_frame_widen >> goal_assum (drule_at Any) >> decide_tac) >>
  `q.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
       (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next`) >> simp[]) >>
  `LIST_REL (log_data_source cx b cap q) xs t` by
    (irule log_data_sources_kept >> goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand buf q = SOME (n2w b)` by
    (drule_all log_write_frame_operand >> simp[]) >>
  `EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sn x) xs` by
    (irule log_data_fresh_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `LIST_REL (\arg v. !tv w. ~is_word_type (SND arg) /\
     evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
     eval_operand (FST arg) q = SOME w ==>
     w2n w + val_store_size tv v <= q.vs_alloca_next) xs t` by
    (qpat_assum `LIST_REL (\arg v. !tv w. _) xs t` mp_tac >>
     qpat_assum `EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sa x) xs` mp_tac >>
     simp_tac bool_ss [LIST_REL_EL_EQN, EVERY_EL] >>
     strip_tac >> strip_tac >> simp[] >>
     qx_gen_tac `i` >> strip_tac >>
     `!x. FST (EL i xs) = Var x ==> not_fresh_at sa x` by
       (qpat_x_assum `!n. n < LENGTH xs ==> (\(op,ty). _) _`
          (qspec_then `i` mp_tac) >> simp[] >>
        Cases_on `EL i xs` >> simp[]) >>
     `eval_operand (FST (EL i xs)) q = eval_operand (FST (EL i xs)) s` by
       (irule log_write_frame_operand >>
        goal_assum (drule_at (Pat `log_write_frame _ _ _ _ _`)) >> simp[]) >>
     simp[] >>
     qpat_x_assum `!n. n < LENGTH xs ==> !tv w. _` (qspec_then `i` mp_tac) >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sn sb) q` by
    (first_x_assum irule >> simp[] >>
     (conj_tac >- metis_tac[not_fresh_at_mono]) >>
     (conj_tac >- (qexists_tac `off + type_memory_bytes ce ty` >> simp[])) >>
     qexists_tac `t` >> simp[] >>
     qpat_x_assum `LIST_REL (\arg v. !tv w. _) xs t` mp_tac >> simp[]) >>
  suspend "append"
QED
Resume compile_log_store_data_mem_ok[append]:
  drule buffer_store_memory_shape >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  `emitted_insts sa sn = emitted_insts sa sm ++ emitted_insts sm sn` by
    (irule emitted_insts_append >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sn) s` by
    (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[]) >>
  `EVERY (supported_scalar_type o SND) xs` by
    (irule log_data_sources_types >> goal_assum (drule_at Any)) >>
  drule_all compile_log_store_data_shape >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sn ++ emitted_insts sn sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_x_assum `emitted_insts sa sn = _` kall_tac >>
  asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[]
QED
Finalise compile_log_store_data_mem_ok

Theorem log_scalar_rounded_store_bound:
  supported_scalar_type ty /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  (!n. ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
        (?str. v = StringV str /\ n = LENGTH str)) ==>
       w2n w + 32 + 32 * ((n + 31) DIV 32) <= s.vs_alloca_next) ==>
  w2n w + val_store_size tv v <= s.vs_alloca_next
Proof
  strip_tac >>
  `is_bytestring_type ty` by metis_tac[log_scalar_topic_shape] >>
  Cases_on `ty` >> fs[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_bytestring_type_def] >>
  Cases_on `v` >>
  gvs[vyperValueTheory.evaluate_type_def, vyperTypingTheory.value_has_type_def,
      val_store_size_def, vfmConstantsTheory.word_size_def, AllCaseEqs()] >>
  fs[is_word_type_def]
QED

Theorem log_data_sources_rounded_bound:
  !xs vs. LIST_REL (log_data_source cx b cap s) xs vs /\
  LIST_REL (\arg v. !w n. ~is_word_type (SND arg) /\
    eval_operand (FST arg) s = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w + 32 + 32 * ((n+31) DIV 32) <= s.vs_alloca_next) xs vs ==>
  LIST_REL (\arg v. !tv w. ~is_word_type (SND arg) /\
    evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
    eval_operand (FST arg) s = SOME w ==>
    w2n w + val_store_size tv v <= s.vs_alloca_next) xs vs
Proof
  Induct >> Cases_on `vs` >> simp[] >> rpt strip_tac
  >- (rename1 `log_data_source cx b cap s arg v` >>
      Cases_on `arg` >> gvs[log_data_source_def] >>
      rename1 `supported_scalar_type ty` >>
      irule log_scalar_rounded_store_bound >>
      simp[] >> metis_tac[]) >>
  first_x_assum irule >> simp[]
QED

Theorem compile_log_store_data_frontier:
  compile_log_store_data ce xs buf off sa = ((),sb) /\
  LIST_REL (log_data_source cx b cap s) xs vs /\
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sa x) xs /\
  (!x. buf = Var x ==> not_fresh_at sa x) /\
  eval_operand buf s = SOME (n2w b) /\
  off + SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= cap /\
  b + cap < dimword (:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all compile_log_store_data_run >> strip_tac >>
  gvs[stmtSimLogDataFrameTheory.log_write_frame_def] >>
  qpat_x_assum `_ with <|vs_memory := _; vs_vars := _|> = _`
    (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next`) >> simp[]
QED

Theorem compile_log_store_data_run_mem:
  compile_log_store_data ce xs buf off sa = ((),sb) /\
  LIST_REL (log_data_source cx b cap s) xs vs /\
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sa x) xs /\
  (!x. buf = Var x ==> not_fresh_at sa x) /\
  eval_operand buf s = SOME (n2w b) /\
  off + SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= cap /\
  b + cap < dimword (:256) /\ b + cap <= s.vs_alloca_next /\
  LIST_REL (\arg v. !w n. ~is_word_type (SND arg) /\
    eval_operand (FST arg) s = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w + 32 + 32 * ((n+31) DIV 32) <= s.vs_alloca_next) xs vs ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_alloca_next = s.vs_alloca_next /\
    log_data_layout cx (MAP SND xs) vs (b+off) t.vs_memory /\
    LIST_REL (log_data_source cx b cap t) xs vs /\
    eval_operand buf t = SOME (n2w b) /\
    (!op ty. MEM (op,ty) xs ==> eval_operand op t = eval_operand op s)
Proof
  strip_tac >> drule_all log_data_sources_rounded_bound >> strip_tac >>
  conj_tac >- (irule compile_log_store_data_mem_ok >>
    goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_all compile_log_store_data_run >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  irule compile_log_store_data_frontier >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem log_alloc_buffer_run_frontier:
  compile_alloc_buffer n sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, step_alloca_eq, AllCaseEqs()] >>
  gvs[update_var_def]
QED

Theorem log_allocate_store_prepare_mem:
  compile_alloc_buffer srccap source_st = (srcbuf,start) /\
  compile_log_store_data ce xs srcbuf.buf_operand 0 start = ((),stored_st) /\
  compile_alloc_buffer outcap stored_st = (dst,prepared) /\
  fn_has_code source_st start func /\ fn_has_code stored_st prepared func /\
  ~block_is_terminated source_st /\ ~block_is_terminated stored_st /\
  stmt_state_rel ctx func ce cx es before /\
  stmt_state_rel ctx func ce cx es stored /\
  fresh_vars_wrt source_st before /\ fresh_vars_wrt stored_st stored /\
  srccap < dimword (:256) /\ outcap < dimword (:256) /\
  run_inst_seq (emitted_insts source_st start) before = OK initial /\
  run_inst_seq (emitted_insts start stored_st) initial = OK stored /\
  LIST_REL (log_data_source cx b srccap initial) xs vs /\
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at start x) xs /\
  (!x. srcbuf.buf_operand = Var x ==> not_fresh_at start x) /\
  eval_operand srcbuf.buf_operand initial = SOME (n2w b) /\
  SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= srccap /\
  b + srccap < dimword (:256) /\ b + srccap <= initial.vs_alloca_next /\
  LIST_REL (\arg v. !w n. ~is_word_type (SND arg) /\
    eval_operand (FST arg) initial = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w + 32 + 32 * ((n+31) DIV 32) <= initial.vs_alloca_next) xs vs ==>
  run_inst_seq_mem_ok
    (emitted_insts source_st start ++ emitted_insts start stored_st ++
     emitted_insts stored_st prepared) before /\
  (!t. run_inst_seq
    (emitted_insts source_st start ++ emitted_insts start stored_st ++
     emitted_insts stored_st prepared) before = OK t ==>
    before.vs_alloca_next <= t.vs_alloca_next)
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts source_st start) before` by
    (irule compile_alloc_buffer_body_mem_ok >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts stored_st prepared) stored` by
    (irule compile_alloc_buffer_body_mem_ok >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_all log_data_sources_rounded_bound >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts start stored_st) initial` by
    (irule compile_log_store_data_mem_ok >>
     goal_assum (drule_at (Pat `compile_log_store_data _ _ _ _ _ = _`)) >>
     qexistsl_tac [`b`,`srccap`,`cx`,`vs`] >> simp[]) >>
  `stored.vs_alloca_next = initial.vs_alloca_next` by
    (irule compile_log_store_data_frontier >>
     goal_assum (drule_at (Pat `compile_log_store_data _ _ _ _ _ = _`)) >>
     qexistsl_tac [`b`,`srccap`,`cx`,`vs`] >> simp[]) >>
  `before.vs_alloca_next <= initial.vs_alloca_next` by
    (drule_all log_alloc_buffer_run_frontier >> simp[]) >>
  `run_inst_seq (emitted_insts source_st start ++
      emitted_insts start stored_st) before = OK stored` by
    metis_tac[run_inst_seq_append] >>
  conj_tac
  >- (irule run_inst_seq_mem_ok_append >> simp[] >>
      irule run_inst_seq_mem_ok_append >> simp[]) >>
  rpt strip_tac >>
  `run_inst_seq (emitted_insts stored_st prepared) stored = OK t` by
    metis_tac[run_inst_seq_append] >>
  drule_all log_alloc_buffer_run_frontier >> simp[]
QED
