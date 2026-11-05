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
  cheat
QED

Theorem log_encode_safe_straight[local]:
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) code ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code
Proof
  cheat
QED

Theorem log_topic_straight[local]:
  compile_encode_log_topic ptr_op flag sa = (op,sb) ==>
  inst_extends sa sb /\ same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  cheat
QED

Theorem log_topics_straight[local]:
  !xs sa ops sb. compile_log_topic_ops xs sa = (ops,sb) ==>
  inst_extends sa sb /\ same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  cheat
QED

Theorem log_alloc_straight[local]:
  compile_alloc_buffer cap sa = (buf,sb) ==>
  inst_extends sa sb /\ same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  cheat
QED

Theorem log_emit_straight[local]:
  emit_inst LOG ops [] sa = ((),sb) ==>
  inst_extends sa sb /\ same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  cheat
QED

Theorem log_tuple_encoder_straight[local]:
  EVERY supported_scalar_type tys /\
  compile_abi_encode_to_buf dst src
    (type_to_abi_enc_info sf ce (TupleT tys)) sa = (out,sb) ==>
  inst_extends sa sb /\ same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  cheat
QED

Theorem log_success_suffix_code:
  ce.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_log_eval_all ce args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  EVERY (supported_scalar_type o SND) xs /\ LENGTH flags = LENGTH xs ==>
  inst_extends sm sb /\ same_blocks sm sb /\ sm.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sb)
Proof
  cheat
QED

