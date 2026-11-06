Theory ctorAbiActualLabelEmpty
Ancestors
  ctorAbiActualObservations ctorAbiActualWorld ctorAbiActualNarrow
  abiDecoderEmpty abiDecoderComplexGuard abiDecoderComplexHead abiDecoderGuard
  abiDecoderReentry abiDecoderDynamicLoopSetup abiDecoderVarSequence
  abiDecoderContract abiDecoderLoop fragExec instIdxIndep compileEnv
  abiEncoderRegisteredEffect venomState venomExecSemantics venomInst words list arithmetic

Theorem ctor_actual_complex_guard_labels_fragment[local]:
  abi_decode_complex_head_guard src hi head_sz st = ((),st') /\
  eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + head_sz <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
      abi_encoder_registered_effect {} [] initial t /\ t.vs_labels = initial.vs_labels) (K F)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_complex_guard_reentry >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  `abi_encoder_registered_effect {} [] initial actual` by
    (irule ctor_actual_empty_effect >> gvs[abi_decoder_address_frame_def]) >>
  qexists `actual` >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx,
      abi_encoder_registered_effect_def]
QED

Theorem ctor_actual_empty_complex_labels_reach:
  compile_abi_decode_to_buf dst src opc hi (DecComplex dynamic []) st = ((),st') /\
  fn_has_code st st' func /\ eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    abi_encoder_registered_effect {} [] initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\ actual.vs_labels = initial.vs_labels
Proof
  simp_tac bool_ss [abi_decode_empty_complex_phases] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`head_sz` |-> `0:num`] ctor_actual_complex_guard_labels_fragment) >>
  (impl_tac >- simp[]) >> disch_then assume_tac >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qexists `actual` >> gvs[abi_decoder_address_frame_def]
QED
