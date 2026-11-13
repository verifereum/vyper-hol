Theory stmtLogDataMemory
Ancestors
  stmtSimLogDataRun stmtSimLogDataFrame stmtSimLogData stmtSimLogTopics
  stmtLogTopicsMemory bodyCopyMemory bodyAllocMemory abiBuiltinAllocation stmtReasonMemory exprSimHash exprSimProps
  exprSimBufferStore exprSimDefs supportedTypes context emitHelperProps
  fragExecMem instMemFrontier valueEncoding words list arithmetic compileEnv exprLoweringProps moduleLoweringProps venomInst venomState freshWrites
  typedCopyRankPathMem bodyDeclMemoryCounted placeMemoryCopyEffect fragGasMode
  annassignRelayoutSource typedMemoryCopy valueCopyBytes exprSimMemDefs
  fragGasPathFrameMem typedLogFieldChecked bytesCopyProps exprSimAggregateLoops
  memoryLayoutDefs memoryLayoutRel memoryLayoutSource memoryValueEncoding wideningZeroLayout
  placeMemoryPrimitiveForward fragGasPathMem vyperEventArgCompat rich_list
  eventLoweringStructure stmtLowering fragExec loweringPosts

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
  compile_log_store_data ce xs (MAP SND xs) buf off sa = ((),sb) /\
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
  drule_all compile_log_store_data_scalar_split >> strip_tac >>
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
  compile_log_store_data ce xs (MAP SND xs) buf off sa = ((),sb) /\
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
  compile_log_store_data ce xs (MAP SND xs) buf off sa = ((),sb) /\
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
  compile_log_store_data ce xs (MAP SND xs) srcbuf.buf_operand 0 start = ((),stored_st) /\
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
     goal_assum (drule_at (Pat `compile_log_store_data _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`b`,`srccap`,`cx`,`vs`] >> simp[]) >>
  `stored.vs_alloca_next = initial.vs_alloca_next` by
    (irule compile_log_store_data_frontier >>
     goal_assum (drule_at (Pat `compile_log_store_data _ _ _ _ _ _ = _`)) >>
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

(* Equal actual types; bulk-copy bounds are stronger than logical footprints. *)
Theorem log_equal_type_store_mem_ok:
  compile_store_memory ce src dst ty ty sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  expr_val_rel cx ty v src s /\ expr_store_bound cx ty v src s /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand dst s = SOME d /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (~is_word_type ty /\ ~is_bytestring_type ty ==>
   !sw. eval_operand src s = SOME sw ==>
     type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (gvs[compile_store_memory_def] >>
      drule emitted_insts_emit_void >> strip_tac >>
      simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE] >>
      `type_memory_size tv = 32` by metis_tac[word_tv_memory_size] >> gvs[]) >>
  `?sw. eval_operand src s = SOME sw /\
        val_in_memory tv v (w2n sw) s.vs_memory` by
    gvs[loweringPostsTheory.expr_val_rel_def] >>
  Cases_on `is_bytestring_type ty`
  >- (`?len. mload (w2n sw) s = n2w len /\
             val_store_size tv v = 32 + 32 * word_size len` by
        metis_tac[buffer_typed_bytestring_header] >>
      `val_store_size tv v <= type_memory_size tv` by metis_tac[val_store_size_le] >>
      `w2n sw + val_store_size tv v <= s.vs_alloca_next` by
        (fs[exprSimMemDefsTheory.expr_store_bound_def] >>
         qpat_x_assum `!tv'. _` (qspec_then `tv` mp_tac) >> simp[]) >>
      gvs[compile_store_memory_def] >>
      irule compile_store_bytestring_body_mem_ok >>
      qexistsl_tac [`d`, `dst`, `len`, `src`, `sw`] >> simp[] >>
      rpt strip_tac >> gvs[] >> decide_tac) >>
  Cases_on `type_memory_size tv = 0`
  >- gvs[compile_store_memory_def, compile_copy_memory_def, comp_return_def,
         emitted_insts_def, run_inst_seq_mem_ok_def] >>
  `w2n sw + type_memory_size tv <= s.vs_alloca_next` by metis_tac[] >>
  gvs[compile_store_memory_def] >>
  irule compile_copy_memory_body_mem_ok >>
  qexistsl_tac [`d`, `dst`, `type_memory_size tv`, `src`, `sw`] >> simp[]
QED

Theorem log_data_store_aggregate_mem_ok:
  (if is_word_type ty then emit_void MSTORE [dst;src]
   else if is_bytestring_type ty then compile_store_bytestring src dst
   else emit_void MCOPY [dst;src;Lit (n2w (type_memory_bytes ce ty))]) sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  expr_val_rel cx ty v src s /\ expr_store_bound cx ty v src s /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\ eval_operand dst s = SOME d /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (~is_word_type ty /\ ~is_bytestring_type ty ==>
   !sw. eval_operand src s = SOME sw ==>
     type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (irule log_equal_type_store_mem_ok >>
      goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
      qexistsl_tac [`ce`,`d`,`dst`,`src`,`v`] >>
      gvs[compile_store_memory_def] >> metis_tac[]) >>
  Cases_on `is_bytestring_type ty`
  >- (irule log_equal_type_store_mem_ok >>
      goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
      qexistsl_tac [`ce`,`d`,`dst`,`src`,`v`] >>
      gvs[compile_store_memory_def] >> metis_tac[]) >>
  gvs[] >> drule emitted_insts_emit_void >> strip_tac >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MCOPY, eval_operand_def,
       w2n_n2w] >> metis_tac[]
QED

Theorem log_store_bounds_frame:
  log_write_frame st b cap s t /\
  (!x. op = Var x ==> not_fresh_at st x) /\
  expr_store_bound cx ty v op s /\
  (!w. ~is_word_type ty /\ ~is_bytestring_type ty /\
     eval_operand op s = SOME w ==>
     type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= s.vs_alloca_next) ==>
  expr_store_bound cx ty v op t /\
  (!w. ~is_word_type ty /\ ~is_bytestring_type ty /\
     eval_operand op t = SOME w ==>
     type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= t.vs_alloca_next)
Proof
  strip_tac >> drule_all log_write_frame_operand >> strip_tac >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (fs[log_write_frame_def] >>
     qpat_x_assum `_ with <|vs_memory := _; vs_vars := _|> = _`
       (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next`) >> simp[]) >>
  gvs[exprSimMemDefsTheory.expr_store_bound_def]
QED

Theorem log_data_memory_sources_kept[local]:
  !xs vs.
  LIST_REL (\(op,ty) v. ?tv.
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes ce ty = type_memory_size tv /\
    expr_val_rel cx ty v op s /\ expr_store_bound cx ty v op s /\
    log_source_apart cx b cap (op,ty) v s /\
    (!w. ~is_word_type ty /\ ~is_bytestring_type ty /\ eval_operand op s = SOME w ==>
      type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= s.vs_alloca_next)) xs vs /\
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at st x) xs /\
  log_write_frame st b cap s t ==>
  LIST_REL (\(op,ty) v. ?tv.
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes ce ty = type_memory_size tv /\
    expr_val_rel cx ty v op t /\ expr_store_bound cx ty v op t /\
    log_source_apart cx b cap (op,ty) v t /\
    (!w. ~is_word_type ty /\ ~is_bytestring_type ty /\ eval_operand op t = SOME w ==>
      type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= t.vs_alloca_next)) xs vs
Proof
  Induct_on `xs` >- simp[] >>
  gen_tac >> PairCases_on `h` >> Cases_on `vs` >> simp[] >>
  rpt gen_tac >> strip_tac
  >- (drule_all log_source_value_kept >> strip_tac >>
      drule_all log_source_apart_kept >> strip_tac >>
      qexists_tac `tv` >> simp[] >>
      metis_tac[log_store_bounds_frame, ADD_COMM]) >>
  first_x_assum irule >> simp[]
QED

(* The semantic field run is supplied independently of memory counting. *)
Theorem compile_log_store_data_aggregate_mem_ok:
  (!src ty dst sm sn start s off tv v.
    emit_op ADD [buf; Lit (n2w off)] start = (dst,sm) /\
    (if is_word_type ty then emit_void MSTORE [dst;src]
     else if is_bytestring_type ty then compile_store_bytestring src dst
     else emit_void MCOPY [dst;src;Lit (n2w (type_memory_bytes ce ty))]) sm = ((),sn) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes ce ty = type_memory_size tv /\ expr_val_rel cx ty v src s /\
    eval_operand buf s = SOME (n2w b) /\ b + off < dimword (:256) /\
    type_memory_bytes ce ty < dimword (:256) /\
    (!x. src = Var x ==> not_fresh_at start x) ==>
    inst_extends start sm /\ inst_extends sm sn /\ start.cs_next_var <= sn.cs_next_var /\
    ?q. run_inst_seq (emitted_insts start sn) s = OK q /\
      log_write_frame start (b+off) (type_memory_bytes ce ty) s q) ==>
  !xs vs off sa sb s.
  compile_log_store_data ce xs (MAP SND xs) buf off sa = ((),sb) /\
  LIST_REL (\(op,ty) v. ?tv.
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes ce ty = type_memory_size tv /\
    expr_val_rel cx ty v op s /\ expr_store_bound cx ty v op s /\
    log_source_apart cx b cap (op,ty) v s /\
    (!w. ~is_word_type ty /\ ~is_bytestring_type ty /\ eval_operand op s = SOME w ==>
      type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= s.vs_alloca_next)) xs vs /\
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sa x) xs /\
  (!x. buf = Var x ==> not_fresh_at sa x) /\
  eval_operand buf s = SOME (n2w b) /\
  off + SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= cap /\
  b + cap < dimword (:256) /\ b + cap <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  disch_then (mk_asm "head") >>
  `!src ty dst sm sn start s off tv v.
    emit_op ADD [buf; Lit (n2w off)] start = (dst,sm) /\
    compile_store_memory ce src dst ty ty sm = ((),sn) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes ce ty = type_memory_size tv /\ expr_val_rel cx ty v src s /\
    eval_operand buf s = SOME (n2w b) /\ b + off < dimword (:256) /\
    type_memory_bytes ce ty < dimword (:256) /\
    (!x. src = Var x ==> not_fresh_at start x) ==>
    inst_extends start sm /\ inst_extends sm sn /\ start.cs_next_var <= sn.cs_next_var /\
    ?q. run_inst_seq (emitted_insts start sn) s = OK q /\
      log_write_frame start (b+off) (type_memory_bytes ce ty) s q` by
    (rpt gen_tac >> strip_tac >>
     Cases_on `is_word_type ty`
     >- (asm "head" irule >> gvs[compile_store_memory_def] >> metis_tac[]) >>
     Cases_on `is_bytestring_type ty`
     >- (asm "head" irule >> gvs[compile_store_memory_def] >> metis_tac[]) >>
     Cases_on `type_memory_bytes ce ty`
     >- (gvs[compile_store_memory_def, compile_copy_memory_def, comp_return_def] >>
         drule_all log_data_address_value >> strip_tac >>
         drule emit_op_extends >> strip_tac >>
         drule log_data_address_shape >> strip_tac >>
         (conj_tac >- simp[inst_extends_def]) >>
         (conj_tac >- simp[inst_extends_def, same_blocks_def, emitted_insts_def]) >>
         `t.vs_memory = s.vs_memory` by
           (qpat_assum `t with vs_vars := _ = s`
             (mp_tac o Q.AP_TERM `\z. z.vs_memory`) >> simp[]) >>
         simp[log_write_frame_def] >>
         qpat_assum `t with vs_vars := _ = s`
           (mp_tac o Q.AP_TERM `\z. z with vs_memory := s.vs_memory`) >> simp[]) >>
     asm "head" (qspecl_then [`src`,`ty`] mp_tac) >> simp[] >>
     disch_then irule >>
     fs[compile_store_memory_def] >>
     qpat_x_assum `SUC _ = _` (fn th => fs[GSYM th, compile_copy_memory_def]) >>
     metis_tac[]) >>
  pop_assum (mk_asm "actual_head") >>
  Induct_on `xs`
  >- (simp[stmtLoweringTheory.compile_log_store_data_def, comp_return_def] >>
      rpt strip_tac >> gvs[emitted_insts_def, run_inst_seq_mem_ok_def]) >>
  gen_tac >> PairCases_on `h` >> Cases_on `vs` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `expr_val_rel cx ty v src s` >>
  qpat_x_assum `compile_log_store_data _ _ _ _ _ _ = _` mp_tac >>
  simp[Once stmtLoweringTheory.compile_log_store_data_def,
       comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `emit_op ADD [buf; Lit (n2w off)] sa` >> simp[] >>
  rename1 `emit_op ADD [buf; Lit (n2w off)] sa = (dst,sm)` >>
  Cases_on `compile_store_memory ce src dst ty ty sm` >>
  rename1 `_ sm = (a,sn)` >> Cases_on `a` >> simp[] >> strip_tac >> fs[] >>
  `b + off < dimword (:256) /\ type_memory_bytes ce ty < dimword (:256)` by decide_tac >>
  asm "actual_head" drule_all >> strip_tac >>
  suspend "head_memory"
QED
Resume compile_log_store_data_aggregate_mem_ok[head_memory]:
  drule_all log_data_address_value >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  drule log_data_address_shape >> strip_tac >>
  `u.vs_alloca_next = s.vs_alloca_next /\ u.vs_memory = s.vs_memory /\
   u.vs_labels = s.vs_labels` by
    (qpat_assum `_ with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. (z.vs_alloca_next,z.vs_memory,z.vs_labels)`) >> simp[]) >>
  `eval_operand src u = eval_operand src s` by
    (Cases_on `src` >> gvs[eval_operand_def]) >>
  `expr_val_rel cx ty v src u /\ expr_store_bound cx ty v src u` by
    gvs[loweringPostsTheory.expr_val_rel_def, exprSimMemDefsTheory.expr_store_bound_def] >>
  `run_inst_seq_mem_ok (emitted_insts sm sn) u` by
    (irule log_equal_type_store_mem_ok >>
     goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
     qexistsl_tac [`ce`,`n2w (b+off)`,`dst`,`src`,`v`] >>
     simp[w2n_n2w] >> metis_tac[not_fresh_at_mono, ADD_COMM]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    (drule emitted_insts_emit_op >> strip_tac >>
     simp[run_inst_seq_mem_ok_last, below_frontier_no_ranges, mk_inst_def]) >>
  suspend "tail_memory"
QED
Resume compile_log_store_data_aggregate_mem_ok[tail_memory]:
  gvs[] >>
  `log_write_frame sa b cap s q` by
    (irule log_write_frame_widen >> goal_assum (drule_at Any) >> decide_tac) >>
  drule_all (SRULE [ADD_COMM] log_data_memory_sources_kept) >> strip_tac >>
  `q.vs_alloca_next = s.vs_alloca_next` by
    (fs[log_write_frame_def] >>
     qpat_x_assum `_ with <|vs_memory := _; vs_vars := _|> = _`
       (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next`) >> simp[]) >>
  `eval_operand buf q = SOME (n2w b)` by
    (drule_all log_write_frame_operand >> simp[]) >>
  `EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sn x) xs` by
    (irule log_data_fresh_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sn sb) q` by
    (first_x_assum irule >> simp[] >>
     (conj_tac >- metis_tac[not_fresh_at_mono]) >>
     (conj_tac >- (qexists_tac `off + type_memory_bytes ce ty` >> simp[])) >>
     qexists_tac `t` >> gvs[]) >>
  suspend "append_memory"
QED
Resume compile_log_store_data_aggregate_mem_ok[append_memory]:
  `emitted_insts sa sn = emitted_insts sa sm ++ emitted_insts sm sn` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sn) s` by
    (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[]) >>
  drule compile_log_store_data_aggregate_shape >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sn ++ emitted_insts sn sb` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  qpat_x_assum `emitted_insts sa sn = _` kall_tac >>
  asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[]
QED
Finalise compile_log_store_data_aggregate_mem_ok

Theorem log_declared_same_type_effect_mem[local]:
  compile_store_memory cenv src dst ty ty sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\ expr_val_rel cx ty v src s /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\ eval_operand dst s = SOME dw /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  expr_store_bound cx ty v src s /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    val_in_memory tv v (w2n dw) t.vs_memory /\
    typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size tv)
Proof
  strip_tac >> drule_all buffer_store_memory_encoding >> strip_tac >>
  drule_all buffer_store_memory_capacity >> strip_tac >>
  drule buffer_store_memory_shape >> strip_tac >>
  drule log_declared_same_type_opcodes >> strip_tac >>
  drule compile_store_memory_same_type_no_gas >> strip_tac >>
  `~is_word_type ty /\ ~is_bytestring_type ty ==>
   !sw. eval_operand src s = SOME sw ==>
     type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next` by
    (rpt strip_tac >>
     `val_footprint tv v = type_memory_size tv` by
       metis_tac[nonbytes_evaluated_val_footprint] >>
     `val_store_size tv v = type_memory_size tv` by
       (mp_tac (Q.SPECL [`tv`,`v`] val_footprint_le_store_size) >>
        mp_tac (Q.SPECL [`tv`,`v`] val_store_size_le) >> simp[] >> decide_tac) >>
     gvs[expr_store_bound_def] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule_all log_equal_type_store_mem_ok >> simp[]) >>
  `gas_path_mem ctx func s 0
    (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >>
     qexists_tac `sa` >> simp[] >>
     gvs[EVERY_MEM] >> metis_tac[]) >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[typed_copy_effect_def, gas_marked_path_def,
      venom_state_component_equality, lookup_var_def] >>
  conj_tac >- (drule_all gas_path_mem_exec >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >> gvs[same_blocks_def]
QED
Theorem log_declared_store_effect_mem[local]:
  compile_store_memory cenv src dst dty sty sa = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  event_arg_compatible dty lty /\ type_widens_to (get_tenv cx) lty dty /\
  (~is_word_type dty /\ ~is_bytestring_type dty ==> sty = lty) /\
  evaluate_type (get_tenv cx) lty = SOME ltv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type ltv v /\ value_has_type dtv v /\
  val_wf ltv v /\ val_wf dtv v /\ expr_val_rel cx lty v src s /\
  log_source_apart cx (w2n dw) (type_memory_bytes cenv dty) (src,lty) v s /\
  eval_operand dst s = SOME dw /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  w2n dw + type_memory_bytes cenv dty < dimword (:256) /\
  expr_store_bound cx lty v src s /\
  w2n dw + type_memory_bytes cenv dty <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_bytes cenv dty)
Proof
  strip_tac >>
  `type_memory_bytes cenv dty = type_memory_size dtv` by
    (irule typed_copy_memory_size >> simp[] >> qexists_tac `get_tenv cx` >>
     simp[] >> metis_tac[]) >>
  `type_memory_size dtv < dimword (:256)` by decide_tac >>
  Cases_on `is_word_type dty`
  >- (`dty = lty` by metis_tac[word_event_compatible_same] >> gvs[] >>
      `compile_store_memory cenv src dst dty dty sa = ((),sb)` by
        gvs[compile_store_memory_def] >>
      simp[] >> irule log_declared_same_type_effect_mem >> simp[] >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  Cases_on `is_bytestring_type dty`
  >- (`is_bytestring_type lty` by metis_tac[event_arg_compatible_bytestring] >>
      `~is_word_type lty` by metis_tac[is_bytestring_word_type] >>
      `compile_store_memory cenv src dst dty dty sa = ((),sb)` by
        gvs[compile_store_memory_def] >>
      `expr_val_rel cx dty v src s` by
        (irule expr_val_rel_compatible >> metis_tac[]) >>
      `val_store_size ltv v = val_store_size dtv v` by
        metis_tac[bytestring_val_store_size_eq] >>
      `expr_store_bound cx dty v src s` by
        gvs[expr_store_bound_def] >>
      simp[] >> irule log_declared_same_type_effect_mem >> simp[] >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  gvs[] >> Cases_on `dty = lty`
  >- (gvs[] >> simp[] >> irule log_declared_same_type_effect_mem >> simp[] >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  `~is_word_type lty /\ ~is_bytestring_type lty` by
    (gvs[event_arg_compatible_alias_def] >>
     metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type,
               memoryLocalRhsPropsTheory.arg_type_fits_bytestring_target]) >>
  `?sw. eval_operand src s = SOME sw /\
        val_in_memory ltv v (w2n sw) s.vs_memory` by gvs[expr_val_rel_def] >>
  `val_footprint ltv v = type_memory_size ltv` by
    metis_tac[nonbytes_evaluated_val_footprint] >>
  `val_store_size ltv v = type_memory_size ltv` by
    (mp_tac (Q.SPECL [`ltv`,`v`] val_footprint_le_store_size) >>
     mp_tac (Q.SPECL [`ltv`,`v`] val_store_size_le) >> simp[] >> decide_tac) >>
  `type_memory_size ltv <> 0` by metis_tac[type_widens_to_zero_layout] >>
  `w2n sw + type_memory_size ltv <= s.vs_alloca_next` by
    gvs[expr_store_bound_def] >>
  `w2n sw + type_memory_size ltv < dimword (:256)` by decide_tac >>
  `lty <> dty` by metis_tac[] >>
  drule_all log_declared_source_separated >> simp[] >> disch_then assume_tac >>
  Cases_on `tuple_memory_layout_eq dty lty`
  >- suspend "bulk" >>
  `compile_store_memory_typed cenv dst dty src lty sa = ((),sb)` by
    gvs[compile_store_memory_def] >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `tenv` |-> `get_tenv cx`,
      `sty` |-> `lty`, `stv` |-> `ltv`, `fn` |-> `func`]
    (SPEC_ALL compile_store_memory_typed_path_mem)) >>
  (impl_tac >- (simp[ADD_COMM, DISJ_COMM] >>
    conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >> metis_tac[])) >>
  strip_tac >>
  qexists_tac `t` >> simp[] >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    metis_tac[gas_path_mem_memory_length] >>
  qpat_assum `gas_path_mem ctx func s 0 (OK t)`
    (assume_tac o CONJUNCT1 o MATCH_MP gas_path_mem_exec) >>
  gvs[typed_copy_effect_def, gas_marked_path_def, venom_state_component_equality,
      ADD_COMM] >>
  qx_genl_tac [`a`,`len`] >> disch_tac >>
  qpat_x_assum `!p k. _ ==> mem_bytes_at p k t.vs_memory = _`
    (qspecl_then [`a`,`len`] mp_tac) >> simp[ADD_COMM]
QED
Resume log_declared_store_effect_mem[bulk]:
  `memory_layout_key dty = memory_layout_key lty` by
    (Cases_on `dty` >> Cases_on `lty` >>
     gvs[tuple_memory_layout_eq_def, memory_layout_key_tuple]) >>
  `memory_layout_rel dtv ltv` by metis_tac[memory_layout_key_evaluated] >>
  `type_memory_size dtv = type_memory_size ltv` by
    gvs[memory_layout_rel_def] >>
  `val_in_memory dtv v (w2n sw) s.vs_memory` by
    (irule memory_value_rel_val_in_memory >> simp[] >>
     irule memory_layout_rel_value >> qexists_tac `ltv` >> simp[] >>
     irule val_in_memory_memory_value_rel >> simp[]) >>
  `expr_val_rel cx dty v src s` by gvs[expr_val_rel_def] >>
  `compile_store_memory cenv src dst dty dty sa = ((),sb)` by
    gvs[compile_store_memory_def] >>
  `val_footprint dtv v = type_memory_size dtv` by
    metis_tac[nonbytes_evaluated_val_footprint] >>
  `val_store_size dtv v = type_memory_size dtv` by
    (mp_tac (Q.SPECL [`dtv`,`v`] val_footprint_le_store_size) >>
     mp_tac (Q.SPECL [`dtv`,`v`] val_store_size_le) >> simp[] >> decide_tac) >>
  `expr_store_bound cx dty v src s` by gvs[expr_store_bound_def] >>
  mp_tac (Q.INST [`ty` |-> `dty`, `tv` |-> `dtv`]
    (SPEC_ALL log_declared_same_type_effect_mem)) >>
  (impl_tac >- (simp[ADD_COMM] >> metis_tac[])) >> simp[]
QED
Finalise log_declared_store_effect_mem

Theorem log_declared_field_effect_mem[local]:
  compile_log_store_data cenv [(src,sty)] [dty] buf off sa = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  event_arg_compatible dty lty /\ type_widens_to (get_tenv cx) lty dty /\
  (~is_word_type dty /\ ~is_bytestring_type dty ==> sty = lty) /\
  evaluate_type (get_tenv cx) lty = SOME ltv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type ltv v /\ value_has_type dtv v /\
  val_wf ltv v /\ val_wf dtv v /\ expr_val_rel cx lty v src s /\
  log_source_apart cx (w2n bw + off) (type_memory_bytes cenv dty) (src,lty) v s /\
  eval_operand buf s = SOME bw /\
  (!x. buf = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ (!lab. src <> Label lab) /\
  w2n bw + off + type_memory_bytes cenv dty <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) /\
  expr_store_bound cx lty v src s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    val_in_memory dtv v (w2n bw + off) t.vs_memory /\
    typed_copy_effect ctx func sa sb s t (w2n bw + off) (type_memory_bytes cenv dty)
Proof
  strip_tac >>
  qpat_x_assum `compile_log_store_data _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_log_store_data_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  Cases_on `emit_op ADD [buf; Lit (n2w off)] sa` >> simp[] >>
  rename1 `emit_op ADD [buf; Lit (n2w off)] sa = (dst,sm)` >> strip_tac >>
  Cases_on `compile_store_memory cenv src dst dty sty sm` >>
  rename1 `compile_store_memory cenv src dst dty sty sm = (unit,sn)` >>
  Cases_on `unit` >> gvs[] >>
  `cs_extends sa sm` by metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `cs_extends sm sb` by
    metis_tac[ci_mono_compile_store_memory, ci_mono_def, pairTheory.SND] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule log_data_address_shape >> strip_tac >>
  `eval_operand buf s = SOME (n2w (w2n bw))` by simp[] >>
  drule_all log_data_address_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK raw` >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    (drule emitted_insts_emit_op >> strip_tac >>
     simp[run_inst_seq_mem_ok_last, below_frontier_no_ranges, mk_inst_def]) >>
  `same_blocks sa sm /\
   sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sm)` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def] >> strip_tac >>
     gvs[same_blocks_def, emitted_insts_def, DROP_APPEND,
         mk_inst_def, is_terminator_def]) >>
  `gas_path_mem ctx func s 0
      (OK (raw with vs_inst_idx := LENGTH sm.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  qpat_assum `gas_path_mem ctx func s 0 _`
    (assume_tac o CONJUNCT1 o MATCH_MP gas_path_mem_exec) >>
  qabbrev_tac `u = raw with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  `eval_operand dst u = SOME (n2w (w2n bw+off)) /\
    typed_copy_effect ctx func sa sm s u (w2n bw+off) (type_memory_bytes cenv dty)` by
    (gvs[Abbr `u`, typed_copy_effect_def, gas_marked_path_def,
         eval_operand_def, lookup_var_def, same_blocks_def] >>
     gvs[venom_state_component_equality] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "store"
QED
Resume log_declared_field_effect_mem[store]:
  `expr_val_rel cx lty v src u /\
   log_source_apart cx (w2n bw+off) (type_memory_bytes cenv dty) (src,lty) v u` by
    (irule log_declared_effect_source >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[ADD_COMM]) >>
  `eval_operand src u = eval_operand src s` by
    (irule log_declared_effect_operand >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    (drule typed_copy_effect_record >>
     disch_then (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next`) >> simp[]) >>
  `expr_store_bound cx lty v src u` by gvs[expr_store_bound_def] >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
   u.vs_inst_idx = LENGTH sm.cs_current_insts` by
    gvs[typed_copy_effect_def] >>
  `w2n bw+off < dimword (:256)` by decide_tac >>
  `?t. gas_path_mem ctx func u 0 (OK t) /\
    val_in_memory dtv v (w2n bw+off) t.vs_memory /\
    typed_copy_effect ctx func sm sb u t (w2n bw+off) (type_memory_bytes cenv dty)` by
    (`w2n (n2w (w2n bw+off):256 word) = w2n bw+off` by
       simp[wordsTheory.w2n_n2w] >>
     `?t. gas_path_mem ctx func u 0 (OK t) /\
       val_in_memory dtv v (w2n (n2w (w2n bw+off):256 word)) t.vs_memory /\
       typed_copy_effect ctx func sm sb u t (w2n (n2w (w2n bw+off):256 word))
         (type_memory_bytes cenv dty)` suffices_by metis_tac[] >>
     irule log_declared_store_effect_mem >>
     simp[] >> goal_assum (drule_at Any) >> simp[ADD_COMM] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[ADD_COMM]) >>
  qexists_tac `t` >> conj_tac >- metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  conj_tac >- metis_tac[ADD_COMM] >>
  irule typed_copy_effect_then >> qexistsl_tac [`sm`, `sm`, `u`] >>
  conj_tac >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
    goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >> metis_tac[ADD_COMM]
QED
Finalise log_declared_field_effect_mem
Theorem compile_log_store_data_declared_path_mem:
compile_log_store_data cenv ops dtys buf off sa = ((),sb) /\
LENGTH ops = LENGTH ltys /\ LENGTH ops = LENGTH dtys /\
acyclic_struct_metadata cenv.ce_struct_fields /\
sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
(!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
  ALL_DISTINCT (MAP FST fields) /\
  EVERY (\(fname,fty,sz). !tv.
    evaluate_type (get_tenv cx) fty = SOME tv ==>
    sz = type_memory_size tv) fields) /\
LIST_REL (\((op,sty),(lty,dty)) v.
  event_arg_compatible dty lty /\
  type_widens_to (get_tenv cx) lty dty /\
  (~is_word_type dty /\ ~is_bytestring_type dty ==> sty = lty) /\
  (?ltv dtv. evaluate_type (get_tenv cx) lty = SOME ltv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type ltv v /\ value_has_type dtv v /\
    val_wf ltv v /\ val_wf dtv v) /\
  expr_val_rel cx lty v op s /\
  expr_store_bound cx lty v op s /\
  log_source_apart cx (w2n bw + off)
    (SUM (MAP (type_memory_bytes cenv) dtys)) (op,lty) v s)
  (ZIP (ops, ZIP (ltys,dtys))) vs /\
eval_operand buf s = SOME bw /\
(!x. buf = Var x ==> not_fresh_at sa x) /\
EVERY (\p. (!x. FST p = Var x ==> not_fresh_at sa x) /\
             (!lab. FST p <> Label lab)) ops /\
w2n bw + off + SUM (MAP (type_memory_bytes cenv) dtys) <= s.vs_alloca_next /\
s.vs_alloca_next < dimword (:256) /\
fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
?t. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  log_data_layout cx dtys vs (w2n bw + off) t.vs_memory /\
  (!p k. p+k <= w2n bw + off \/
     w2n bw + off + SUM (MAP (type_memory_bytes cenv) dtys) <= p ==>
     mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
    vs_prev_bb := s.vs_prev_bb|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  map_every qid_spec_tac [`s`,`sb`,`sa`,`off`,`vs`,`dtys`,`ltys`,`ops`] >>
  Induct_on `ops`
  >- (rpt gen_tac >> simp[compile_log_store_data_def, comp_return_def] >>
      strip_tac >> gvs[log_data_layout_def, compile_log_store_data_def, comp_return_def] >>
      qexists_tac `s` >> simp[log_data_layout_def, venom_state_component_equality] >>
      irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  Cases_on `h` >> rename1 `(src,sty)::ops` >>
  Cases_on `ltys` >> Cases_on `dtys` >> Cases_on `vs` >>
  simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `event_arg_compatible dty lty` >>
  rename1 `expr_val_rel cx lty v src s` >>
  rename1 `LIST_REL _ (ZIP (ops,ZIP (ltail,dtys))) vtail` >>
  rename1 `compile_log_store_data cenv ((src,sty)::ops) (dty::dtys) buf off sa = ((),sb)` >>
  drule (iffLR compile_log_store_data_split) >> strip_tac >>
  `cs_extends sa mid /\ cs_extends mid sb` by
    metis_tac[compile_log_store_data_ci_mono, ci_mono_def, pairTheory.SND] >>
  drule_all fn_has_code_split >> strip_tac >>
  `log_source_apart cx (w2n bw+off) (type_memory_bytes cenv dty) (src,lty) v s` by
    (gvs[log_source_apart_def] >> rpt strip_tac >>
     first_x_assum drule_all >> decide_tac) >>
  `?u. gas_path_mem ctx func s 0 (OK u) /\
    val_in_memory dtv v (w2n bw+off) u.vs_memory /\
    typed_copy_effect ctx func sa mid s u (w2n bw+off) (type_memory_bytes cenv dty)` by
    (qpat_x_assum `!ltys dtys vs off sa sb s. _` kall_tac >>
     irule log_declared_field_effect_mem >> goal_assum (drule_at Any) >> simp[] >>
     rpt conj_tac >> TRY decide_tac >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[ADD_COMM]) >>
  `u.vs_labels = s.vs_labels /\ u.vs_alloca_next = s.vs_alloca_next` by
    (drule typed_copy_effect_record >>
     disch_then (mp_tac o AP_TERM ``\s. (s.vs_labels,s.vs_alloca_next)``) >> simp[]) >>
  `eval_operand buf u = SOME bw` by
    (Cases_on `buf` >> gvs[eval_operand_def] >>
     metis_tac[typed_copy_effect_lookup]) >>
  `~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
   u.vs_inst_idx = LENGTH mid.cs_current_insts` by
    metis_tac[typed_copy_effect_endpoint] >>
  suspend "tail"
QED
Resume compile_log_store_data_declared_path_mem[tail]:
  qpat_x_assum `!ltys dtys vs off sa sb s. _`
    (qspecl_then [`ltail`, `dtys`, `vtail`, `off + type_memory_bytes cenv dty`,
                 `mid`, `sb`, `u`] mp_tac) >>
  (impl_tac
   >- (simp[] >>
       conj_tac >- first_assum ACCEPT_TAC >>
       conj_tac >-
        (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
         simp[LIST_REL_EL_EQN, EL_ZIP] >> strip_tac >>
         rpt strip_tac >>
         qpat_x_assum `!n. _` (qspec_then `n` mp_tac) >> simp[] >>
         Cases_on `EL n ops` >> simp[] >> strip_tac >>
         `(!x. q = Var x ==> not_fresh_at sa x) /\ (!lab. q <> Label lab)` by
           (qpat_x_assum `EVERY _ ops` mp_tac >>
            simp[EVERY_EL] >> disch_then (qspec_then `n` mp_tac) >> simp[]) >>
         `eval_operand q u = eval_operand q s` by
           metis_tac[log_declared_effect_operand] >>
         `log_source_apart cx (w2n bw+off) (type_memory_bytes cenv dty)
            (q,EL n ltail) (EL n vtail) s` by
           (gvs[log_source_apart_def] >> rpt strip_tac >>
            first_x_assum drule_all >> decide_tac) >>
         simp[] >> conj_tac
         >- metis_tac[log_declared_effect_source] >>
         conj_tac >- gvs[expr_store_bound_def] >>
         pure_rewrite_tac[log_source_apart_def] >> rpt strip_tac >>
         qpat_x_assum `log_source_apart cx _ (SUM _ + _) (q,_) _ s`
           (mp_tac o REWRITE_RULE [log_source_apart_def]) >>
         simp[] >> disch_then (qspec_then `w` mp_tac) >> gvs[] >>
         decide_tac) >>
       `sa.cs_next_var <= mid.cs_next_var` by
         metis_tac[compile_log_store_data_ci_mono, ci_mono_def, pairTheory.SND] >>
       conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
       qpat_x_assum `EVERY _ ops` mp_tac >>
       simp[EVERY_EL] >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono])) >>
  strip_tac >>
  rename1 `gas_path_mem ctx func u 0 (OK result)` >>
  `typed_copy_effect ctx func mid sb u result
      (w2n bw+off+type_memory_bytes cenv dty)
      (SUM (MAP (type_memory_bytes cenv) dtys))` by
    (qpat_assum `gas_path_mem ctx func u 0 (OK result)`
       (assume_tac o CONJUNCT1 o MATCH_MP gas_path_mem_exec) >>
     `LENGTH u.vs_memory <= LENGTH result.vs_memory` by
       metis_tac[gas_path_mem_memory_length] >>
     `result.vs_allocas = u.vs_allocas` by
       (qpat_assum `_ = u`
          (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >> simp[]) >>
     pure_rewrite_tac[typed_copy_effect_def, gas_marked_path_def, COND_CLAUSES] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (qpat_assum `u.vs_current_bb = _` (fn bb =>
        qpat_assum `u.vs_inst_idx = _` (fn idx =>
        qpat_assum `_ = u` mp_tac >>
        simp_tac (srw_ss()) [bb, idx]))) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (pure_rewrite_tac[ADD_ASSOC] >>
        qpat_assum `!p k. _ ==> mem_bytes_at p k result.vs_memory = _`
          (ACCEPT_TAC o PURE_REWRITE_RULE [ADD_ASSOC])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "join"
QED
Resume compile_log_store_data_declared_path_mem[join]:
  `type_memory_bytes cenv dty = type_memory_size dtv` by
    (irule typed_copy_memory_size >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[EVERY_MONOTONIC]) >>
  `val_in_memory dtv v (w2n bw+off) result.vs_memory` by
    (qpat_assum `typed_copy_effect ctx func mid sb u result _ _`
       (fn eff => irule (MATCH_MP
          (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] log_declared_effect_head_frame)
          (PURE_REWRITE_RULE [ADD_ASSOC] eff))) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `type_memory_bytes cenv dty = _`
       (fn sz => pure_rewrite_tac[sz, LESS_EQ_REFL])) >>
  `typed_copy_effect ctx func sa sb s result (w2n bw+off)
      (type_memory_bytes cenv dty + SUM (MAP (type_memory_bytes cenv) dtys))` by
    (`sa.cs_next_var <= mid.cs_next_var` by
       metis_tac[compile_log_store_data_ci_mono, ci_mono_def, pairTheory.SND] >>
     irule typed_copy_effect_then >> qexistsl_tac [`mid`,`mid`,`u`] >>
     conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
     conj_tac >> irule typed_copy_effect_enlarge >>
     goal_assum (drule_at Any) >> decide_tac) >>
  qexists_tac `result` >>
  `gas_path_mem ctx func s 0 (OK result)` by
    metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  gvs[typed_copy_effect_def, gas_marked_path_def, log_data_layout_def,
      ADD_ASSOC, ADD_COMM] >> metis_tac[]
QED
Finalise compile_log_store_data_declared_path_mem
