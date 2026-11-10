(* Option-valued observations of allocation-free primitive decoder code. *)
Theory decoderPrimitiveObservations
Ancestors
  abiDecoderClampedWord abiDecoderBytesTyped abiDecoderBytesFrame
  abiDecoderReentryPointer abiDecoderReentry abiDecoderVarSequence
  abiEncoder emitHelper emitHelperProps exprLoweringProps compileEnv
  venomState venomInst venomExecSemantics
  ctorAbiActualAlloc abiDecoderSequenceReach decoderWorldFramePtr
  list rich_list arithmetic abiDecoderBytesPhases abiDecoderGuards abiDecoderContract
  ctorAbiActualObservations calldataDynOwned abiDecoderComposition

Theorem decoder_word_old_outputs:
  compile_abi_decode_to_buf dst src opc (Lit 0w) (Lit 0w)
    (DecPrimWord clamp) sa = ((),sb) /\ not_fresh_at sa x ==>
  EVERY (\i. ~MEM x i.inst_outputs) (emitted_insts sa sb)
Proof
  Cases_on `clamp` >>
  FIRST [rename1 `IntClamp bits signed` >> Cases_on `signed`, all_tac] >>
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
    compile_abi_decode_static_def, compile_abi_clamp_basetype_def,
    compile_abi_int_clamp_def, compile_abi_bytes_clamp_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >>
  fs[not_fresh_at_def] >> rpt conj_tac >> first_x_assum irule >> decide_tac
QED

Theorem decoder_bytes_old_outputs:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring n) sa = ((),sb) /\ not_fresh_at sa x ==>
  EVERY (\i. ~MEM x i.inst_outputs) (emitted_insts sa sb)
Proof
  simp[abi_decode_bytes_position_sentinel, abi_decode_source_opcode_def,
    compile_abi_dec_addr_def, abi_decode_count_guard_def,
    abi_decode_copy_opcode_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >>
  fs[not_fresh_at_def] >> rpt conj_tac >> first_x_assum irule >> decide_tac
QED

Theorem decoder_primitive_code_shape:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) di sa = ((),sb) /\
  ((?clamp. di = DecPrimWord clamp) \/ (?n. di = DecBytestring n)) ==>
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  inst_extends sa sb /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  strip_tac >> gvs[] >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def]
  >- (drule_all abi_decoder_clamped_word_shape >> strip_tac >>
      drule_all abi_decoder_word_reentry_code >> strip_tac >>
      fs[inst_extends_def, IS_PREFIX_APPEND, EVERY_MEM] >>
      simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  fs[inst_extends_def, IS_PREFIX_APPEND] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND]
QED

Theorem decoder_primitive_old_operand:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) di sa = ((),sb) /\
  ((?clamp. di = DecPrimWord clamp) \/ (?n. di = DecBytestring n)) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  abi_decoder_operand_live sa.cs_next_var op ==>
  eval_operand op t = eval_operand op s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all decoder_primitive_code_shape >> strip_tac >>
  `t.vs_labels = s.vs_labels` by metis_tac[ctor_actual_sequence_labels] >>
  Cases_on `op` >> simp[eval_operand_def] >>
  `not_fresh_at sa s'` by metis_tac[calldata_operand_live_not_fresh] >>
  irule ctor_actual_sequence_var_frame >>
  qexists `emitted_insts sa sb` >> simp[] >>
  `EVERY (\i. ~MEM s' i.inst_outputs) (emitted_insts sa sb)` by
    (qpat_x_assum `(?clamp. _) \/ _` strip_assume_tac >> gvs[] >>
     metis_tac[decoder_word_old_outputs, decoder_bytes_old_outputs]) >>
  fs[EVERY_MEM]
QED
