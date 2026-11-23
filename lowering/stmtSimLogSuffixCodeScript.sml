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

Theorem log_topics_straight:
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
