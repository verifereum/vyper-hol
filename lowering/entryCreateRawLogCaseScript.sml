(* The LOG suffix only owns its installed administrative instructions. *)
Theory entryCreateRawLogCase
Ancestors
  entryCreateAdminSequence entryCreateEffectFocus
  bodyFullRawLogCompose bodyFullRawLogFixedCompose
  bodyPtrMakeArrayAllocBuffer exprLoweringProps emitHelperProps
  exprSimAbiGasBridge createSizeCutCode abiEncoderProps venomInst compileEnv list rich_list
Libs pairLib

Theorem create_raw_log_fixed_tail_layout:
  emit_inst MSTORE [buf;data] [] sn = ((),s1) /\
  emit_inst LOG logops [] s1 = ((),sb) ==>
  sb.cs_current_bb = sn.cs_current_bb /\
  sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb /\
  EVERY (\i. i.inst_id IN frag_ids sn sb /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
    ~MEM i.inst_opcode [CREATE;CREATE2]) (emitted_insts sn sb)
Proof
  strip_tac >>
  qpat_assum `emit_inst MSTORE _ _ _ = _` (strip_assume_tac o MATCH_MP emit_inst_extends) >>
  qpat_assum `emit_inst LOG _ _ _ = _` (strip_assume_tac o MATCH_MP emit_inst_extends) >>
  asm_rewrite_tac[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, frag_ids_def, mk_inst_def, is_terminator_def]
QED

Theorem create_raw_log_dynamic_tail_layout:
  emit_op MLOAD [data] sn = (len,s1) /\
  emit_op ADD [data;Lit 32w] s1 = (ptr_op,s2) /\
  emit_inst LOG logops [] s2 = ((),sb) ==>
  sb.cs_current_bb = sn.cs_current_bb /\
  sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb /\
  EVERY (\i. i.inst_id IN frag_ids sn sb /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
    ~MEM i.inst_opcode [CREATE;CREATE2]) (emitted_insts sn sb)
Proof
  strip_tac >>
  qpat_assum `emit_op MLOAD _ _ = _` (strip_assume_tac o MATCH_MP emit_op_extends) >>
  qpat_assum `emit_op ADD _ _ = _` (strip_assume_tac o MATCH_MP emit_op_extends) >>
  drule emit_inst_extends >> strip_tac >>
  fs[same_blocks_def] >>
  qpat_assum `emit_op MLOAD _ _ = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  qpat_assum `emit_op ADD _ _ = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  qpat_x_assum `s1.cs_current_insts = _` kall_tac >>
  qpat_x_assum `s2.cs_current_insts = _` kall_tac >>
  gvs[] >> asm_rewrite_tac[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, frag_ids_def, mk_inst_def, is_terminator_def]
QED

Theorem create_raw_log_fixed_scratch_layout:
  compile_alloc_buffer 32 sm = (buf,sd) ==>
  sd.cs_current_bb = sm.cs_current_bb /\
  sd.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sd /\
  EVERY (\i. i.inst_id IN frag_ids sm sd /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
    ~MEM i.inst_opcode [CREATE;CREATE2]) (emitted_insts sm sd)
Proof
  simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule emit_op_extends >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  fs[same_blocks_def, frag_ids_def, mk_inst_def, is_terminator_def]
QED
