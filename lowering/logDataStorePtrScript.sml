(* List-level robust source and staging composition. *)
Theory logDataStorePtr
Ancestors robustCopyTransportPtr logValueFramePtr loweringPosts exprSimDefs exprSimProps logDataFieldPtr logDataFieldRunPtr logFieldGhostPtr logInstSeqPtr stmtSimLogDataRun
  stmtSimLogDataFrame stmtSimLogData stmtSimLogTopics bodyPtrDefs ptrDiscipline
  exprLoweringProps context stmtLowering emitHelper emitHelperProps freshWrites venomInst venomState compileEnv words list arithmetic

Theorem log_data_sources_ptr_kept:
  !xs vs. LIST_REL (log_data_source cx b cap s) xs vs /\
  LIST_REL (\(op,ty) v. ptr_val_ok cx ty v op G tn s) xs vs /\
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at st x) xs /\
  log_write_frame st b cap s t /\
  (!p. not_fresh_at st p ==>
    FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p)) /\
  (!i. ~(b <= i /\ i < b+cap) ==> (i IN tm.t_mem <=> i IN tn.t_mem)) ==>
  LIST_REL (\(op,ty) v. ptr_val_ok cx ty v op H tm t) xs vs
Proof
  Induct_on `xs` >- simp[] >>
  gen_tac >> PairCases_on `h` >> Cases_on `vs` >> simp[] >> strip_tac >>
  conj_tac
  >- (irule log_data_source_ptr_kept >>
      qexistsl_tac [`G`,`b`,`cap`,`s`,`st`,`tn`] >>
      simp[] >> Cases_on `h0` >> gvs[op_taint_def] >> metis_tac[]) >>
  first_x_assum irule >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem log_data_layout_exterior_transport:
  !tys vs p.
    EVERY supported_scalar_type tys /\
    (!m. mem_agree_outside tn mem m ==> log_data_layout cx tys vs p m) /\
    (!i. p <= i /\ i < p + SUM (MAP (type_memory_bytes ce) tys) ==>
      mem_bytes_at i 1 mem' = mem_bytes_at i 1 mem /\
      (i IN tm <=> i IN tn)) ==>
    !m. mem_agree_outside tm mem' m ==> log_data_layout cx tys vs p m
Proof
  Induct_on `tys`
  >- (Cases_on `vs` >> simp[log_data_layout_def] >> rpt strip_tac >>
      first_x_assum (qspec_then `mem` mp_tac) >> simp[mem_agree_outside_def]) >>
  Cases_on `vs` >> simp[log_data_layout_def]
  >- (rpt strip_tac >> first_x_assum (qspec_then `mem` mp_tac) >>
      simp[mem_agree_outside_def]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `supported_scalar_type ty` >>
  rename1 `log_data_layout cx tys rest (p + type_memory_size _) _` >>
  rename1 `val_wf _ v` >>
  `mem_agree_outside tn mem mem` by simp[mem_agree_outside_def] >>
  `?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v` by
    (first_x_assum (qspec_then `mem` mp_tac) >> simp[] >> metis_tac[]) >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    metis_tac[log_scalar_memory_size] >>
  `!m. mem_agree_outside tn mem m ==>
     val_in_memory tv v p m /\
     log_data_layout cx tys rest (p+type_memory_size tv) m` by metis_tac[optionTheory.SOME_11] >>
  rpt gen_tac >> strip_tac >> simp[] >> suspend "head"
QED
Resume log_data_layout_exterior_transport[head]:
  irule robust_val_in_memory_exterior_frame >> conj_tac >- simp[] >>
  qexistsl_tac [`mem`,`mem'`,`tn`,`tm`,
    `{i | ~(p <= i /\ i < p+type_memory_size tv)}`] >> simp[] >>
  `val_footprint tv v <= type_memory_size tv` by metis_tac[val_footprint_le] >>
  rpt strip_tac >> decide_tac
QED
Finalise log_data_layout_exterior_transport

Theorem log_store_memory_opcode_shape:
  supported_scalar_type ty /\ compile_store_memory ce src dst ty ty sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  strip_tac >> Cases_on `is_bytestring_type ty`
  >- (`~is_word_type ty` by metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
      `compile_store_bytestring src dst sa = ((),sb)` by gvs[compile_store_memory_def] >>
      drule logBytesCodePtrTheory.compile_store_bytestring_opcodes >>
      simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[is_terminator_def]) >>
  `is_word_type ty` by metis_tac[log_scalar_topic_shape] >>
  `emit_void MSTORE [dst;src] sa = ((),sb)` by gvs[compile_store_memory_def] >>
  drule emitted_insts_emit_void >> simp[mk_inst_def,is_terminator_def]
QED

Theorem log_data_store_opcode_shape:
  !xs buf off sa sb. EVERY (supported_scalar_type o SND) xs /\
  compile_log_store_data ce xs buf off sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  Induct_on `xs`
  >- simp[compile_log_store_data_def,comp_return_def,emitted_insts_def] >>
  gen_tac >> PairCases_on `h` >> simp[] >> rpt gen_tac >> strip_tac >>
  drule_all compile_log_store_data_split >> strip_tac >>
  drule emit_op_extends >> strip_tac >> drule log_data_address_shape >> strip_tac >>
  drule exprSimBufferStoreTheory.buffer_store_memory_shape >> strip_tac >>
  `emitted_insts sa sn = emitted_insts sa sm ++ emitted_insts sm sn` by
    (irule emitted_insts_append >> asm_rewrite_tac[]) >>
  `sn.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sn` by
    (asm_rewrite_tac[] >> simp[APPEND_ASSOC]) >>
  `sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb` by
    (drule_all compile_log_store_data_shape >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa sn ++ emitted_insts sn sb` by
    (irule emitted_insts_append >> asm_rewrite_tac[]) >>
  simp[EVERY_APPEND] >> conj_tac
  >- (conj_tac
      >- (drule emitted_insts_emit_op >> strip_tac >>
          simp[mk_inst_def,is_terminator_def]) >>
      irule log_store_memory_opcode_shape >> metis_tac[]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem log_data_source_inst_idx[simp]:
  log_data_source cx b cap (s with vs_inst_idx := k) = log_data_source cx b cap s
Proof
  simp[FUN_EQ_THM] >> gen_tac >> PairCases_on `x` >>
  simp[log_data_source_def,log_source_apart_def,expr_val_rel_def,
    eval_operand_def,lookup_var_def]
QED

Theorem ptr_val_ok_inst_idx[simp]:
  ptr_val_ok cx ty v op G tn (s with vs_inst_idx := k) <=>
  ptr_val_ok cx ty v op G tn s
Proof
  simp[ptr_val_ok_def,ptr_mem_ok_def,eval_operand_def,lookup_var_def] >>
  Cases_on `op` >> simp[eval_operand_def,lookup_var_def]
QED

Theorem log_field_opcode_shape:
  emit_op ADD [buf;Lit (n2w off)] sa = (dst,sm) /\
  compile_store_memory ce src dst ty ty sm = ((),sn) /\ supported_scalar_type ty ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sn)
Proof
  strip_tac >> drule emit_op_extends >> strip_tac >>
  drule exprSimBufferStoreTheory.buffer_store_memory_shape >> strip_tac >>
  `emitted_insts sa sn = emitted_insts sa sm ++ emitted_insts sm sn` by
    (irule emitted_insts_append >> asm_rewrite_tac[]) >>
  simp[EVERY_APPEND] >> conj_tac
  >- (drule emitted_insts_emit_op >> strip_tac >> simp[mk_inst_def,is_terminator_def]) >>
  irule log_store_memory_opcode_shape >> metis_tac[]
QED

Theorem compile_log_store_data_seq_ptr:
  !xs vs off sa sb s G tn.
    compile_log_store_data ce xs (Var buf) off sa = ((),sb) /\
    LIST_REL (log_data_source cx b cap s) xs vs /\
    LIST_REL (\(op,ty) v. ptr_val_ok cx ty v op G tn s) xs vs /\
    EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sa x) xs /\
    not_fresh_at sa buf /\ lookup_var buf s = SOME (n2w b) /\
    ptr_covers G tn buf s cap /\
    off + SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= cap /\
    b+cap < dimword(:256) /\ ~ctx_has_dalloca ctx ==>
    ?H tm t.
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H tm /\
      (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
        log_data_layout cx (MAP SND xs) vs (b+off) m) /\
      log_write_frame sa (b+off)
        (SUM (MAP (type_memory_bytes ce) (MAP SND xs))) s t /\
      (!i. ~(b+off <= i /\ i < b+off+SUM (MAP (type_memory_bytes ce) (MAP SND xs))) ==>
        mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tm.t_mem <=> i IN tn.t_mem)) /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!p. not_fresh_at sa p ==>
        lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
        op_taint tm (Var p) = op_taint tn (Var p))
Proof
  Induct_on `xs`
  >- (simp[compile_log_store_data_def,comp_return_def,emitted_insts_def,
        run_inst_seq_def,fragGasSeqPtrTheory.inst_seq_ptr_def,log_data_layout_def] >>
      rpt strip_tac >> qexistsl_tac [`G`,`tn`,`s`] >> simp[]) >>
  gen_tac >> PairCases_on `h` >> Cases_on `vs` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `supported_scalar_type h1 /\
   ?tv. evaluate_type (get_tenv cx) h1 = SOME tv /\
     value_has_type tv h /\ val_wf tv h` by gvs[log_data_source_def] >>
  drule_all compile_log_store_data_split >> strip_tac >>
  `?dv. dst = Var dv` by metis_tac[emitted_insts_emit_op] >>
  gvs[] >>
  `expr_val_rel cx h1 h h0 s` by gvs[log_data_source_def] >>
  drule log_data_address_shape >> strip_tac >>
  `off + type_memory_bytes ce h1 <= cap` by decide_tac >>
  drule_all log_data_field_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  suspend "tail_ready"
QED
Resume compile_log_store_data_seq_ptr[tail_ready]:
  `log_write_frame sa b cap s sf` by
    (irule log_write_frame_widen >> goal_assum (drule_at Any) >> decide_tac) >>
  `LIST_REL (log_data_source cx b cap sf) xs t` by
    (irule log_data_sources_kept >> goal_assum (drule_at Any) >> simp[]) >>
  `LIST_REL (\(op,ty) v. ptr_val_ok cx ty v op Gf tnf sf) xs t` by
    (irule log_data_sources_ptr_kept >>
     qexistsl_tac [`G`,`b`,`cap`,`s`,`sa`,`tn`] >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sn x) xs` by
    metis_tac[log_data_fresh_mono] >>
  `not_fresh_at sn buf` by metis_tac[not_fresh_at_mono] >>
  `lookup_var buf sf = SOME (n2w b) /\ ptr_covers Gf tnf buf sf cap` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  qabbrev_tac `u = sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sn)` >>
  `LIST_REL (log_data_source cx b cap u) xs t /\
   LIST_REL (\(op,ty) v. ptr_val_ok cx ty v op Gf tnf u) xs t /\
   lookup_var buf u = SOME (n2w b) /\ ptr_covers Gf tnf buf u cap` by
    gvs[Abbr `u`,ptr_covers_def,lookup_var_def] >>
  `off+type_memory_bytes ce h1 + SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= cap` by
    decide_tac >>
  qpat_x_assum `!vs off sa sb s G tn. _` drule_all >>
  disch_then (qx_choose_then `H` (qx_choose_then `tm` (qx_choose_then `z` strip_assume_tac))) >>
  suspend "compose"
QED
Resume compile_log_store_data_seq_ptr[compose]:
  `EVERY (supported_scalar_type o SND) xs` by
    metis_tac[log_data_sources_types] >>
  drule emit_op_extends >> strip_tac >>
  drule exprSimBufferStoreTheory.buffer_store_memory_shape >> strip_tac >>
  drule_all compile_log_store_data_shape >> strip_tac >>
  `emitted_insts sa sn = emitted_insts sa sm ++ emitted_insts sm sn` by
    (irule emitted_insts_append >> asm_rewrite_tac[]) >>
  `sn.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sn` by
    (asm_rewrite_tac[] >> simp[APPEND_ASSOC]) >>
  `emitted_insts sa sb = emitted_insts sa sn ++ emitted_insts sn sb` by
    (irule emitted_insts_append >> asm_rewrite_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sn)` by
    (irule log_field_opcode_shape >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sn sb)` by
    (drule_all log_data_store_opcode_shape >> simp[EVERY_MEM]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK (z with vs_inst_idx := sf.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H tm` by
    (qunabbrev_tac `u` >> drule_all successful_seq_ptr_append >> simp[]) >>
  qexistsl_tac [`H`,`tm`,`z with vs_inst_idx := sf.vs_inst_idx`] >>
  asm_rewrite_tac[] >> conj_tac >- suspend "layout" >>
  conj_tac >- suspend "write_frame" >>
  conj_tac >- suspend "exterior" >>
  simp[] >> gen_tac >> strip_tac >>
  `not_fresh_at sn p` by metis_tac[not_fresh_at_mono] >>
  qpat_x_assum `!p. not_fresh_at sn p ==> _` (qspec_then `p` mp_tac) >>
  qpat_x_assum `!p. not_fresh_at sa p ==> _` (qspec_then `p` mp_tac) >>
  simp[Abbr `u`,lookup_var_def] >> metis_tac[]
QED
Resume compile_log_store_data_seq_ptr[layout]:
  `type_memory_bytes ce h1 = type_memory_size tv` by
    metis_tac[log_scalar_memory_size] >>
  simp[] >> rpt strip_tac >> simp[log_data_layout_def] >>
  reverse conj_tac
  >- (qpat_x_assum `!m. _ ==> log_data_layout _ _ _ _ _` (qspec_then `m` mp_tac) >>
      simp[GSYM ADD_ASSOC]) >>
  irule robust_val_in_memory_exterior_frame >> conj_tac >- simp[] >>
  qexistsl_tac [`sf.vs_memory`,`z.vs_memory`,`tnf.t_mem`,`tm.t_mem`,
    `{i | b+off+type_memory_size tv <= i}`] >> simp[Abbr `u`] >>
  `val_footprint tv h <= type_memory_size tv` by metis_tac[val_footprint_le] >>
  rpt strip_tac >> decide_tac
QED
Resume compile_log_store_data_seq_ptr[write_frame]:
  qpat_assum `compile_log_store_data ce ((_,_)::xs) _ _ sa = _`
    (mp_then Any mp_tac compile_log_store_data_run) >>
  disch_then (qspecl_then [`h::t`,`s`] mp_tac) >>
  simp[eval_operand_def] >>
  disch_then (qspecl_then [`cx`,`cap`,`b`] mp_tac) >>
  `b < dimword(:256)` by decide_tac >> simp[] >>
  strip_tac >>
  `t' = z with vs_inst_idx := sf.vs_inst_idx` by metis_tac[] >>
  metis_tac[]
QED
Resume compile_log_store_data_seq_ptr[exterior]:
  simp[] >> gen_tac >> strip_tac >>
  `~(b+off <= i /\ i < b+off+type_memory_bytes ce h1) /\
   (~(b+(off+type_memory_bytes ce h1) <= i) \/
    ~(i < b+(off+type_memory_bytes ce h1+SUM (MAP (type_memory_bytes ce) (MAP SND xs)))))` by
    decide_tac >>
  qpat_x_assum `!i. _ ==> mem_bytes_at _ _ sf.vs_memory = _ /\ _`
    (qspec_then `i` mp_tac) >>
  qpat_x_assum `!i. _ ==> mem_bytes_at _ _ z.vs_memory = _ /\ _`
    (qspec_then `i` mp_tac) >>
  simp[Abbr `u`] >> metis_tac[]
QED
Finalise compile_log_store_data_seq_ptr

Theorem compile_log_store_data_path_ptr:
  compile_log_store_data ce xs (Var buf) off sa = ((),sb) /\
  LIST_REL (log_data_source cx b cap s) xs vs /\
  LIST_REL (\(op,ty) v. ptr_val_ok cx ty v op G tn s) xs vs /\
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sa x) xs /\
  not_fresh_at sa buf /\ lookup_var buf s = SOME (n2w b) /\
  ptr_covers G tn buf s cap /\
  off + SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= cap /\
  b+cap < dimword(:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb))) H tm
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      log_data_layout cx (MAP SND xs) vs (b+off) m) /\
    log_write_frame sa (b+off)
      (SUM (MAP (type_memory_bytes ce) (MAP SND xs))) s t /\
    (!i. ~(b+off <= i /\ i < b+off+SUM (MAP (type_memory_bytes ce) (MAP SND xs))) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all compile_log_store_data_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `EVERY (supported_scalar_type o SND) xs` by metis_tac[log_data_sources_types] >>
  drule_all log_data_store_opcode_shape >> strip_tac >>
  drule_all fragGasSeqPtrTheory.run_inst_seq_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`H`,`tm`,`t`] >> simp[]
QED

Theorem log_data_write_ghost_inv:
  ghost_inv d ce cx es G tn s /\ local_ptrs_rel fn ce es.scopes s /\
  local_ptrs_reserved ce sa /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!name p sz. local_region ce es.scopes s name p sz ==> p+sz <= b \/ b+n <= p) /\
  log_write_frame sa b n s t /\
  (!i. ~(b <= i /\ i < b+n) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  (!p. not_fresh_at sa p ==>
    lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
    op_taint tm (Var p) = op_taint tn (Var p)) ==>
  ghost_inv d ce cx es H tm t
Proof
  strip_tac >> irule ghost_inv_exterior_transport >>
  qexistsl_tac [`G`,`fn`,`s`,`sa`,`tn`,`{i | b <= i /\ i < b+n}`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> res_tac >> decide_tac) >>
  qpat_x_assum `log_write_frame _ _ _ _ _` mp_tac >>
  simp[log_write_frame_def] >> strip_tac >>
  qpat_x_assum `t with <|vs_memory := _; vs_vars := _|> = s`
    (fn th => map_every (mp_tac o C AP_TERM th)
      [``\z. z.vs_accounts``,``\z. z.vs_transient``,``\z. z.vs_call_ctx``]) >>
  simp[]
QED

Theorem log_data_write_ghost_kept:
  ghost_kept ce es se G0 tn0 s0 G tn /\ se.cs_next_var <= sa.cs_next_var /\
  (!aid p sz. FLOOKUP s0.vs_allocas aid = SOME (p,sz) /\ aid < se.cs_next_id /\
    (!name a k. local_region ce es.scopes s0 name a k ==> p+sz <= a \/ a+k <= p) ==>
    p+sz <= b \/ b+n <= p) /\
  (!name p sz. local_region ce es.scopes s0 name p sz ==> p+sz <= b \/ b+n <= p) /\
  (!i. ~(b <= i /\ i < b+n) ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  (!p. not_fresh_at sa p ==>
    FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p)) ==>
  ghost_kept ce es se G0 tn0 s0 H tm
Proof
  strip_tac >> irule ghost_kept_exterior_transport >>
  qexistsl_tac [`G`,`sa`,`tn`,`{i | b <= i /\ i < b+n}`] >> simp[] >>
  conj_tac >> rpt strip_tac >> res_tac >> decide_tac
QED
