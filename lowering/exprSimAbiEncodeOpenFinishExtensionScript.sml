Theory exprSimAbiEncodeOpenFinishExtension
Ancestors
  exprSimAbiEncodeFinish abiEncoderExtendSim
  abiBuiltinEncodeCode abiBuiltinEncodeCorrect abiEncoderSequence abiDecoderReentry
  exprSimAbiEncodeExecFrame abiEncoderRegisteredEffect abiDecoderContract
  abiDecoderLoop instIdxIndep entrySinkExtraction venomState compileEnv emitHelper
  exprLoweringProps venomInst list rich_list arithmetic abiDecoderVarSequence
  exprSimAbiEncodeFramedBuiltin

Theorem abi_encode_open_finish_opcodes[local]:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st final)
Proof
  Cases_on `mid_size > 0` >>
  simp[abi_builtin_encode_finish_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
    emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem abi_encode_framed_finish_open_extend:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) /\
  fn_has_code st final func /\
  eval_operand buf initial = SOME (n2w p) /\
  eval_operand encoded_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var buf /\ p < dimword (:256) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\
    mload p actual = n2w (len+mid_size) /\
    abi_decode_frame p 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\
    actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect {} [(p,32)] initial actual /\
    abi_encode_exec_frame func initial actual /\
    abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  drule abi_encode_open_finish_opcodes >> strip_tac >>
  drule_all abi_encode_finish_sequence_open >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK encoded` >>
  `abi_encode_exec_frame func initial encoded` by
    (drule_all abi_encode_framed_finish_sequence >> simp[]) >>
  `eval_operand buf encoded = SOME (n2w p)` by
    (first_x_assum irule >> simp[]) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  drule_all abi_encoder_run_sequence_extend_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule_all abi_encoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH final.cs_current_insts` >>
  gvs[abi_decode_frame_def, eval_op_inst_idx, mload_def,
    abi_encoder_registered_effect_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED
