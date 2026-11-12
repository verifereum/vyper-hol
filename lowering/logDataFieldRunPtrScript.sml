(* Compose covered field addressing with the uniform checked scalar store. *)
Theory logDataFieldRunPtr
Ancestors logDataFieldPtr logInstSeqPtr logValueFramePtr stmtSimLogData
  stmtSimLogDataFrame stmtSimLogDataRun stmtSimLogTopics exprSimBufferStore
  emitHelperProps emitHelper exprLoweringProps context freshWrites
  bodyPtrDefs ptrDiscipline ptrSafeRun venomState venomInst
  finite_map words arithmetic list loweringPosts compileEnv

Theorem log_data_store_memory_opcodes:
  compile_store_memory ce src dst ty ty sa = ((),sb) /\ supported_scalar_type ty ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
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

Theorem log_data_field_seq_ptr:
  emit_op ADD [Var buf;Lit (n2w off)] sa = (Var dst,sm) /\
  compile_store_memory cenv src (Var dst) ty ty sm = ((),sb) /\
  supported_scalar_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\ expr_val_rel cx ty v src s /\
  ptr_val_ok cx ty v src G tn s /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  lookup_var buf s = SOME (n2w b) /\ ptr_covers G tn buf s cap /\
  off+type_memory_bytes cenv ty <= cap /\ b+cap < dimword(:256) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (b+off) m) /\
    log_write_frame sa (b+off) (type_memory_bytes cenv ty) s sf /\
    (!i. ~(b+off <= i /\ i < b+off+type_memory_bytes cenv ty) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  drule_all log_data_address_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `eval_operand (Var buf) s = SOME (n2w b)` by simp[eval_operand_def] >>
  drule_all log_data_address_value >> strip_tac >>
  `t = sf` by
    (qpat_x_assum `run_inst_seq _ _ = OK t` mp_tac >> asm_rewrite_tac[] >> simp[]) >>
  qpat_x_assum `t = sf` SUBST_ALL_TAC >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK s1` >>
  qabbrev_tac `u = s1 with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sm)` >>
  suspend "store_ready"
QED
Resume log_data_field_seq_ptr[store_ready]:
  drule log_data_address_shape >> strip_tac >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `u.vs_labels = s.vs_labels` by
    (qpat_assum `s1 with vs_vars := _ = s`
      (mp_tac o AP_TERM ``\z. z.vs_labels``) >> simp[Abbr `u`]) >>
  `eval_operand src u = eval_operand src s /\
   op_taint tnf src = op_taint tn src /\
   (!p. src = Var p ==> FLOOKUP Gf p = FLOOKUP G p)` by
    (Cases_on `src` >> gvs[eval_operand_def,op_taint_def,Abbr `u`,lookup_var_def]) >>
  `ptr_val_ok cx ty v src Gf tnf u` by suspend "source_ptr" >>
  `expr_val_rel cx ty v src u` by
    gvs[expr_val_rel_def,Abbr `u`,eval_operand_def,lookup_var_def] >>
  `(!p. src = Var p ==> not_fresh_at sm p) /\ not_fresh_at sm dst` by metis_tac[] >>
  `lookup_var dst u = SOME (n2w (b+off)) /\
   ptr_covers Gf tnf dst u (type_memory_bytes cenv ty)` by
    gvs[Abbr `u`,lookup_var_def,ptr_covers_def] >>
  `type_memory_bytes cenv ty < dimword(:256)` by decide_tac >>
  drule_all log_data_store_memory_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `G2` (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac)))) >>
  suspend "compose"
QED
Resume log_data_field_seq_ptr[source_ptr]:
  irule ptr_val_ok_footprint_frame >>
  qexistsl_tac [`G`,`s`,`tn`] >>
  simp[Abbr `u`] >> rpt strip_tac >> gvs[]
QED
Resume log_data_field_seq_ptr[compose]:
  drule emit_op_extends >> strip_tac >>
  drule buffer_store_memory_shape >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sm)` by
    (drule emitted_insts_emit_op >> simp[mk_inst_def,is_terminator_def]) >>
  drule_all log_data_store_memory_opcodes >> strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s = OK (s2 with vs_inst_idx := s1.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G2 tn2` by
    (qunabbrev_tac `u` >> drule_all successful_seq_ptr_append >>
     strip_tac >> asm_rewrite_tac[]) >>
  qexistsl_tac [`G2`,`tn2`,`s2 with vs_inst_idx := s1.vs_inst_idx`] >>
  asm_rewrite_tac[] >>
  `b+off < dimword(:256)` by decide_tac >>
  conj_tac >- gvs[] >>
  conj_tac >- suspend "frame" >>
  suspend "post"
QED
Resume log_data_field_seq_ptr[frame]:
  drule_all log_data_field_run >> strip_tac >>
  `q = s2 with vs_inst_idx := s1.vs_inst_idx` by
    (qpat_x_assum `run_inst_seq _ _ = OK q` mp_tac >> asm_rewrite_tac[] >> simp[]) >>
  qpat_x_assum `q = _` SUBST_ALL_TAC >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[log_scalar_memory_size] >>
  pure_rewrite_tac[log_write_frame_def] >> asm_rewrite_tac[]
QED
Resume log_data_field_seq_ptr[post]:
  conj_tac
  >- (qpat_x_assum `!i. _ ==> mem_bytes_at _ _ s2.vs_memory = _ /\ _` mp_tac >>
      simp[Abbr `u`]) >>
  gen_tac >> strip_tac >>
  `not_fresh_at sm p` by metis_tac[] >>
  qpat_x_assum `!p. not_fresh_at sm p ==> _ /\ _ /\ _` (qspec_then `p` mp_tac) >>
  qpat_x_assum `!p. not_fresh_at sa p ==> _ /\ _ /\ _` (qspec_then `p` mp_tac) >>
  simp[Abbr `u`,lookup_var_def] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x s1 = _`
    (qspec_then `p` mp_tac) >> simp[lookup_var_def]
QED
Finalise log_data_field_seq_ptr
