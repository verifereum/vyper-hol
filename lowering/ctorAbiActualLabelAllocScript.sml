Theory ctorAbiActualLabelAlloc
Ancestors
  ctorAbiActualObservations ctorAbiActualNarrow ctorAbiActualAlloc
  ctorAbiActualFrame abiDecoderVarSequence abiDecoderReentry
  abiEncoderRegisteredEffect venomExecSemantics venomState venomInst
  finite_map pred_set list arithmetic words

Theorem ctor_actual_word_alloca_labels_narrow:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit 32w] /\ inst.inst_outputs = [out] /\
  inst.inst_id IN ids /\
  ctor_actual_scratch fn ids d n s /\ d+n <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  unit_alloca_budget ctx < dimword (:256) ==>
  ?t p.
    step_inst_base inst s = OK t /\
    eval_operand (Var out) t = SOME (n2w p) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (p,32) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    regions_disjoint (d,n) (p,32) /\
    ctor_actual_scratch fn ids d n t /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    abi_encoder_registered_effect {inst.inst_id} [] s t /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_labels = s.vs_labels
Proof
  strip_tac >> drule_all ctor_actual_word_alloca_narrow >> strip_tac >>
  `abi_decoder_reentry_opcode inst.inst_opcode` by simp[abi_decoder_reentry_opcode_def] >>
  drule_all ctor_actual_step_labels >> strip_tac >>
  qexistsl [`t`, `p`] >> simp[]
QED

Theorem ctor_actual_index_labels_narrow:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) /\
  st.cs_next_id IN ids /\
  ctor_actual_scratch fn ids d n s /\ d+n <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  unit_alloca_budget ctx < dimword (:256) ==>
  ?t p. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ctor_actual_scratch fn ids d n t /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    abi_encoder_registered_effect {st.cs_next_id} [] s t /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_labels = s.vs_labels
Proof
  strip_tac >> drule_all ctor_actual_index_narrow >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')` by
    (drule ctor_actual_index_insts >> simp[mk_inst_def, abi_decoder_reentry_opcode_def]) >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  qexistsl [`t`, `p`] >> simp[]
QED
