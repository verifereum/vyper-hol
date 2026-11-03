(* Nonallocating canonical array prefix before actual index initialization. *)
Theory ctorAbiActualArrayPrepare
Ancestors
  abiDecoderDynarrayPrefix abiDecoderDynarrayBound abiDecoderGuards
  abiDecoderArrayHeader abiDecoderArrayLoopInit
  abiDecoderReentryPointer abiDecoderReentry abiDecoderVarSequence abiDecoderVarExtend
  abiDecoderDynamicLoopSetup abiDecoderContract abiDecoderGuard abiDecoderReservation
  ctorAbiActualObservations ctorAbiActualWorld abiEncoderRegisteredEffect
  compileEnv emitHelper emitHelperProps exprLoweringProps
  venomState venomExecSemantics venomInst words list rich_list arithmetic
  fragExec instIdxIndep abiDecoderLoop

Theorem ctor_actual_array_prefix_code:
  abi_decode_dynarray_prefix src opc hi maxn asz st = ((),st') /\
  abi_decode_source_opcode opc ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
    ~is_alloca_op i.inst_opcode /\ i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  strip_tac >> gvs[abi_decode_source_opcode_def] >> Cases_on `hi = Lit 0w` >>
  qpat_x_assum `abi_decode_dynarray_prefix _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [abi_decode_dynarray_prefix_def,
    abi_decode_count_guard_def, abi_decode_dynarray_end_guard_def,
    abi_decode_dynarray_end_def, abi_decode_le_guard_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def, mk_inst_def,
    is_terminator_def, is_alloca_op_def]
QED

Theorem ctor_actual_array_prefix_reentry:
  abi_decode_dynarray_prefix src DLOAD hi maxn asz st = ((),st') /\
  eval_operand src initial = SOME (n2w sb) /\
  abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb+32+n*asz <= h /\ h < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect {} [] initial actual /\ inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  mp_tac (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var initial`,
    `opc` |-> `DLOAD`, `abi_sz` |-> `asz`] abi_decode_dynarray_prefix_sequence) >>
  (impl_tac >- (simp[abi_decoder_prune_fresh, abi_decoder_prune_eval,
    abi_decode_load_def, abi_decode_source_def, abi_decoder_prune_vars_def] >>
    qpat_x_assum `hi = Lit 0w \/ _` mp_tac >>
    simp[AC ADD_ASSOC ADD_COMM, AC MULT_ASSOC MULT_COMM])) >>
  strip_tac >> rename1 `fresh_vars_wrt st' clean` >>
  drule_all ctor_actual_array_prefix_code >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')` by
    fs[EVERY_CONJ] >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars clean actual` >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ, is_alloca_op_def] >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  qexists `actual` >>
  gvs[abi_decoder_address_frame_def, abi_decoder_prune_vars_def,
    abi_encoder_registered_effect_def]
QED

Theorem ctor_actual_array_prefix_reach:
  abi_decode_dynarray_prefix src DLOAD hi maxn asz st = ((),st') /\
  eval_operand src initial = SOME (n2w sb) /\
  abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb+32+n*asz <= h /\ h < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect {} [] initial actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_array_prefix_reentry >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all ctor_actual_array_prefix_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `frag_exec ctx st st' (\s. s = initial)
    (\t. fresh_vars_wrt limit_st t /\
      abi_decoder_address_frame st.cs_next_var initial t /\
      t.vs_labels = initial.vs_labels /\
      abi_encoder_registered_effect {} [] initial t) (K F)` by
    (irule frag_exec_run_inst_seq >>
     fs[inst_extends_def, fresh_vars_wrt_def, abi_decoder_address_frame_def,
       eval_op_inst_idx, abi_encoder_registered_effect_def]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >>
  strip_tac >> rename1 `abi_decode_sim ctx func initial result` >>
  qexists `result` >> asm_rewrite_tac[]
QED

Theorem ctor_actual_array_count_header_code:
  abi_decode_array_header dst src DLOAD st = (cnt,st') ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode)
    (emitted_insts st st')
Proof
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
    emit_def] >> strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem ctor_actual_array_count_header_reentry:
  abi_decode_array_header dst src DLOAD st = (cnt,st') /\
  eval_operand src initial = SOME p /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    eval_operand cnt actual = SOME (abi_decode_load DLOAD p initial) /\
    mem_word_at d actual.vs_memory = abi_decode_load DLOAD p initial /\
    fresh_vars_wrt limit_st actual /\
    abi_decode_frame d 32 initial actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect {} [(d,32)] initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  mp_tac (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var initial`,
    `opc` |-> `DLOAD`] abi_decode_array_header_sequence) >>
  (impl_tac >- simp[abi_decoder_prune_fresh, abi_decoder_prune_eval]) >>
  strip_tac >> rename1 `fresh_vars_wrt st' clean` >>
  drule_all ctor_actual_array_count_header_code >> strip_tac >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars clean actual` >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  drule_all abi_decoder_reentry_frame >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_scratch_free_effect >> strip_tac >>
  qexists `actual` >>
  gvs[abi_decoder_address_frame_def, abi_decoder_prune_vars_def,
    abi_decode_load_def] >>
  drule_all abi_decoder_vars_extend_eval >> simp[]
QED

Theorem ctor_actual_array_count_header_reach:
  abi_decode_array_header dst src DLOAD st = (cnt,st') /\
  eval_operand src initial = SOME p /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand cnt actual = SOME (abi_decode_load DLOAD p initial) /\
    mem_word_at d actual.vs_memory = abi_decode_load DLOAD p initial /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d 32 initial actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect {} [(d,32)] initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_array_count_header_reentry >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `frag_exec ctx st st' (\s. s = initial)
    (\t. eval_operand cnt t = SOME (abi_decode_load DLOAD p initial) /\
      mem_word_at d t.vs_memory = abi_decode_load DLOAD p initial /\
      fresh_vars_wrt limit_st t /\ abi_decode_frame d 32 initial t /\
      (!op w. abi_decoder_operand_live st.cs_next_var op /\
        eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_labels = initial.vs_labels /\
      abi_encoder_registered_effect {} [(d,32)] initial t /\
      t.vs_allocas = initial.vs_allocas /\
      t.vs_alloca_next = initial.vs_alloca_next) (K F)` by
    (irule frag_exec_run_inst_seq >>
     fs[inst_extends_def, fresh_vars_wrt_def, abi_decode_frame_def,
       eval_op_inst_idx, abi_encoder_registered_effect_def] >> metis_tac[]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >>
  strip_tac >> rename1 `abi_decode_sim ctx func initial result` >>
  qexists `result` >> asm_rewrite_tac[]
QED
