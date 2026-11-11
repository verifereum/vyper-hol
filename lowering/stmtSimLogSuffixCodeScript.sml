(* Straight-line compiler certificates for the event emission suffix. *)
Theory stmtSimLogSuffixCode
Ancestors
  stmtSimLogTrace stmtSimLogStoreContinue stmtSimLogEncodeFields stmtSimLogSuffix
  stmtSimLogEncodeLayout stmtSimLogTopics abiEncoderProps abiBuiltinAllocation
  fragExec emitHelperProps stmtLowering context list rich_list venomInst
  abiDecoderArrayInit stmtSimLogExecFields emitHelper compileEnv loweringSlice exprLoweringProps
  abiEncoderCounters stmtSimLogDataRun

Theorem log_straight_append[local]:
  inst_extends sa sm /\ inst_extends sm sb /\
  same_blocks sa sm /\ same_blocks sm sb /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sm) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sb) ==>
  inst_extends sa sb /\ same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  strip_tac >> conj_tac
  >- (irule inst_extends_trans >> qexists_tac `sm` >> simp[]) >>
  conj_tac >- gvs[same_blocks_def] >>
  conj_tac >- decide_tac >>
  metis_tac[abi_decoder_emitted_every_append]
QED

Theorem log_encode_safe_straight[local]:
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) code ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code
Proof
  simp[EVERY_MEM, log_encode_safe_opcode_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[is_terminator_def]
QED

Theorem log_topic_straight[local]:
  compile_encode_log_topic ptr_op flag sa = (op,sb) ==>
  inst_extends sa sb /\ same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  Cases_on `flag` >>
  simp[compile_encode_log_topic_def, emit_op_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[same_blocks_def, inst_extends_def, emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem log_topics_straight[local]:
  !xs sa ops sb. compile_log_topic_ops xs sa = (ops,sb) ==>
  inst_extends sa sb /\ same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  Induct
  >- simp[compile_log_topic_ops_def, comp_return_def, inst_extends_def,
       emitted_insts_def, same_blocks_def] >>
  simp[compile_log_topic_ops_def, comp_return_def,
    comp_bind_def] >> rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[] >> drule log_topic_straight >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  irule log_straight_append >> goal_assum (drule_at Any) >> simp[]
QED

Theorem log_alloc_straight[local]:
  compile_alloc_buffer cap sa = (buf,sb) ==>
  inst_extends sa sb /\ same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  simp[same_blocks_def, mk_inst_def, is_terminator_def]
QED

Theorem log_emit_straight[local]:
  emit_inst LOG ops [] sa = ((),sb) ==>
  inst_extends sa sb /\ same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  simp[same_blocks_def, inst_extends_def, emitted_insts_def, DROP_LENGTH_APPEND,
    mk_inst_def, is_terminator_def]
QED

Theorem log_tuple_encoder_straight[local]:
  EVERY supported_scalar_type tys /\
  compile_abi_encode_to_buf dst src
    (type_to_abi_enc_info sf ce (TupleT tys)) sa = (out,sb) ==>
  inst_extends sa sb /\ same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  strip_tac >> drule abi_encoder_counters >> strip_tac >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields (TupleT tys)`
  >- (`EXISTS (\t. is_abi_dynamic ce.ce_struct_fields t) tys` by
        gvs[is_abi_dynamic_def] >>
      `EVERY (\(ei,asz,mz,dyn). log_scalar_enc_info ei)
        (MAP (\t. (type_to_abi_enc_info sf ce t,
          abi_embedded_static_size ce.ce_struct_fields t, type_memory_bytes ce t,
          is_abi_dynamic ce.ce_struct_fields t)) tys)` by
        (irule log_tuple_enc_members_scalar >> simp[]) >>
      gvs[log_tuple_enc_info_selected] >>
      drule log_encode_dynamic_safe >>
      simp[EXISTS_MAP, combinTheory.o_DEF] >> strip_tac >>
      simp[] >> irule log_encode_safe_straight >> simp[]) >>
  gvs[log_tuple_enc_info_selected] >> drule log_encode_copy_safe >> strip_tac >>
  simp[] >> irule log_encode_safe_straight >> simp[]
QED

Theorem log_success_suffix_code:
  ce.ce_event_info (nsid_to_string id) = SOME (h,MAP SND xs,flags) /\
  log_eval_view ce args sa xs sm /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  EVERY (supported_scalar_type o SND) xs /\ LENGTH flags = LENGTH xs ==>
  inst_extends sm sb /\ same_blocks sm sb /\ sm.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sb)
Proof
  strip_tac >> drule log_topics_straight >> strip_tac >>
  Cases_on `SND (split_log_ops xs flags) = []`
  >- (drule_all compile_log_empty_trace >> strip_tac >>
      qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >> simp[] >> strip_tac >>
      drule_all log_emit_straight >> strip_tac >>
      irule log_straight_append >> qexists_tac `st` >> simp[]) >>
  drule_all (SRULE [] (Q.INST [`data_ops` |-> `SND (split_log_ops xs flags)`]
    compile_log_data_trace)) >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >> simp[] >>
  disch_then (qx_choose_then `src` (qx_choose_then `s1` (qx_choose_then `s2`
    (qx_choose_then `dst` (qx_choose_then `s3` (qx_choose_then `len`
      (qx_choose_then `s4` strip_assume_tac))))))) >>
  suspend "data"
QED

Resume log_success_suffix_code[data]:
  `EVERY (supported_scalar_type o SND) (SND (split_log_ops xs flags))` by
    (irule log_split_data_every >> simp[] >> goal_assum (drule_at Any)) >>
  `EVERY supported_scalar_type (MAP SND (SND (split_log_ops xs flags)))` by
    gvs[EVERY_MAP, combinTheory.o_DEF] >>
  drule_all compile_log_store_data_shape >> strip_tac >>
  drule_all log_store_data_safe >> strip_tac >>
  drule log_encode_safe_straight >> strip_tac >>
  imp_res_tac log_alloc_straight >>
  drule_all log_tuple_encoder_straight >> strip_tac >>
  drule log_emit_straight >> strip_tac >>
  `inst_extends s3 sb /\ same_blocks s3 sb /\ s3.cs_next_var <= sb.cs_next_var /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts s3 sb)` by
    (irule log_straight_append >> qexists_tac `s4` >> simp[]) >>
  `inst_extends s2 sb /\ same_blocks s2 sb /\ s2.cs_next_var <= sb.cs_next_var /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts s2 sb)` by
    (irule log_straight_append >> qexists_tac `s3` >> simp[]) >>
  `inst_extends s1 sb /\ same_blocks s1 sb /\ s1.cs_next_var <= sb.cs_next_var /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts s1 sb)` by
    (irule log_straight_append >> qexists_tac `s2` >> simp[]) >>
  `inst_extends st sb /\ same_blocks st sb /\ st.cs_next_var <= sb.cs_next_var /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st sb)` by
    (irule log_straight_append >> qexists_tac `s1` >> simp[]) >>
  irule log_straight_append >> qexists_tac `st` >> simp[]
QED
Finalise log_success_suffix_code
