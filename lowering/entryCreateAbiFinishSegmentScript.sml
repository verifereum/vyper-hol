(* The installed ADD (when present) and length-header MSTORE. *)
Theory entryCreateAbiFinishSegment
Ancestors
  entryCreateAdminSequence entryCreateCompletedCut entryCreateFocusSpec
  bodyFullAbiEncodeFinish abiBuiltinEncodeCode emitHelperProps exprLoweringProps
  abiEncoderProps compileEnv emitHelper fragExec venomInst venomState
  arithmetic list

Theorem abi_encode_finish_fetch_inventory:
  abi_builtin_encode_finish buf lenop k a = ((),b) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> GAS /\
    i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ ~is_terminator i.inst_opcode) (emitted_insts a b)
Proof
  strip_tac >> drule abi_builtin_encode_finish_shape >> strip_tac >>
  Cases_on `0 < k`
  >- (gvs[abi_builtin_encode_finish_def, comp_bind_def] >> pairarg_tac >> gvs[] >>
      drule emit_op_extends >> drule emit_void_extends >> rpt strip_tac >>
      drule_all emitted_insts_append >> strip_tac >>
      simp[APPEND_ASSOC] >>
      drule emitted_insts_emit_op >> drule emitted_insts_emit_void >> rpt strip_tac >>
      simp[frag_ids_def, mk_inst_def, is_terminator_def]) >>
  `k = 0` by decide_tac >> gvs[abi_builtin_encode_finish_def] >>
  drule emitted_insts_emit_void >> simp[frag_ids_def, mk_inst_def, is_terminator_def]
QED

Theorem abi_encode_finish_scoped_phase:
  abi_builtin_encode_finish buf lenop k a = ((),b) /\ fn_has_code a b f /\
  create_operand_at a s ==>
  create_operand_cut a b explicit ctx f tops cx st0 source (es,s) /\
  (!t. ~s.vs_halted /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
    run_inst_seq (emitted_insts a b) s = OK (t with vs_inst_idx := s.vs_inst_idx) ==>
    create_operand_full_scope a b explicit ctx f s [] (OK t))
Proof
  strip_tac >> drule abi_encode_finish_fetch_inventory >> strip_tac >>
  conj_tac >- (irule create_admin_sequence_cut >> fs[EVERY_MEM]) >>
  rpt strip_tac >>
  `t = (t with vs_inst_idx := s.vs_inst_idx) with vs_inst_idx := LENGTH b.cs_current_insts`
    by (simp[venom_state_component_equality] >> fs[]) >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  irule create_admin_sequence_scope >> fs[EVERY_MEM]
QED
