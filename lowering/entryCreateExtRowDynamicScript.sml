Theory entryCreateExtRowDynamic
Ancestors
  entryCreateAdminSequence entryCreatePathScope entryCreateFocusSpec createSizeCutCode
  abiEncodeValuesDynamic abiEncoderWindowJointPhases abiEncoderWindowChild abiEncoderWindowPhase
  abiEncoderChildCode abiEncoderProps exprLoweringProps emitHelperProps emitHelper fragExec compileEnv
  venomInst venomState venomExecSemantics list rich_list arithmetic pair pred_set

(* Setup and publication are straight-line even when the child encodes a loop.
   The list equations below refer to the witnesses chosen by the joint proofs. *)
Theorem dynamic_pack_prefix_code[local]:
  abi_encode_child_prefix dst ho cursor a = (ops,b) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
    (emitted_insts a b)
Proof
  simp[abi_encode_child_prefix_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  simp_tac bool_ss [GSYM listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
  simp[frag_ids_def, mk_inst_def, is_terminator_def]
QED

Theorem dynamic_pack_suffix_code[local]:
  abi_encode_child_suffix head cursor off len a = (out,b) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
    (emitted_insts a b)
Proof
  simp[abi_encode_child_suffix_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  simp_tac bool_ss [GSYM listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
  simp[frag_ids_def, mk_inst_def, is_terminator_def]
QED

Theorem dynamic_pack_normalized_scope[local]:
  fn_has_code a b f /\ b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
    (emitted_insts a b) /\
  create_operand_at a s /\ ~s.vs_halted /\ create_operand_at b t /\
  run_inst_seq (emitted_insts a b) s = OK (t with vs_inst_idx := s.vs_inst_idx) ==>
  create_operand_full_scope a b explicit ctx f s [] (OK t)
Proof
  strip_tac >> drule_all create_admin_sequence_scope >>
  disch_then (qspecl_then [`explicit`,`ctx`] mp_tac) >>
  qpat_assum `create_operand_at b t` (strip_assume_tac o REWRITE_RULE [create_operand_at_def]) >>
  pop_assum (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >> simp[]
QED

Theorem dynamic_pack_prefix_scope:
  abi_encode_child_prefix dst ho cursor a = (ops,b) /\ fn_has_code a b f /\
  create_operand_at a s /\ ~s.vs_halted /\ window_phase ctx f a b ids outs s t /\
  run_inst_seq (emitted_insts a b) s = OK (t with vs_inst_idx := s.vs_inst_idx) ==>
  create_operand_full_scope a b explicit ctx f s [] (OK t)
Proof
  strip_tac >> drule dynamic_pack_prefix_code >> strip_tac >>
  drule window_phase_control >> strip_tac >>
  irule dynamic_pack_normalized_scope >> simp[create_operand_at_def] >>
  metis_tac[create_operand_at_def]
QED

Theorem dynamic_pack_suffix_scope:
  abi_encode_child_suffix head cursor off len a = (out,b) /\ fn_has_code a b f /\
  create_operand_at a s /\ ~s.vs_halted /\ window_phase ctx f a b ids outs s t /\
  run_inst_seq (emitted_insts a b) s = OK (t with vs_inst_idx := s.vs_inst_idx) ==>
  create_operand_full_scope a b explicit ctx f s [] (OK t)
Proof
  strip_tac >> drule dynamic_pack_suffix_code >> strip_tac >>
  drule window_phase_control >> strip_tac >>
  irule dynamic_pack_normalized_scope >> simp[create_operand_at_def] >>
  metis_tac[create_operand_at_def]
QED
