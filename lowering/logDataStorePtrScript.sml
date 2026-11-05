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
