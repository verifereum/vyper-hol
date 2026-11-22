Theory logTopicsNonDalloca
Ancestors
  stmtSimLogTopics stmtLowering context compileEnv emitHelper emitHelperProps
  exprLoweringProps venomInst list rich_list

Triviality log_topic_emitted_non_dalloca:
  compile_encode_log_topic x flag sa = (op,sb) ==>
  EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts sa sb)
Proof
  Cases_on `flag` >>
  simp[compile_encode_log_topic_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem log_topics_emitted_non_dalloca:
  !raw sa ops sb. compile_log_topic_ops raw sa = (ops,sb) ==>
  EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts sa sb)
Proof
  Induct >- simp[compile_log_topic_ops_def, comp_return_def, emitted_insts_def] >>
  rpt gen_tac >> simp[compile_log_topic_ops_cons] >> strip_tac >> gvs[] >>
  drule log_topic_inst_extends >> strip_tac >>
  drule log_topics_inst_extends >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  simp[EVERY_APPEND] >> drule log_topic_emitted_non_dalloca >> simp[]
QED
