Theory exprSimAbiEncodeSetupExtension
Ancestors
  loweringStateRelDefs
  abiEncodeWindowBuiltin abiBuiltinEncodeCorrect abiEncoderExtendSim abiBuiltinEncodeSetup
  abiBuiltinEncodeMethod abiBuiltinEncodeAllocate abiBuiltinEncodeCode
  abiBuiltinSetupFrames abiBuiltinAllocation abiEncoderSequence
  abiDecoderReentry abiDecoderContract abiDecoderLoop instIdxIndep compileEnv entrySinkExtraction
  venomState venomExecSemantics finite_map words list arithmetic

Theorem abi_encode_setup_none_extend[local]:
  abi_builtin_encode_setup NONE maxlen st = (ops,ready) /\ fn_has_code st ready func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,32+32*word_size maxlen)) /\
  32+32*word_size maxlen < dimword (:256) /\ ready.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+32)) /\
    fresh_vars_wrt limit_st actual /\
    abi_builtin_allocation_frame st.cs_next_var st.cs_next_id (32+32*word_size maxlen) initial actual /\
    actual.vs_current_bb = ready.cs_current_bb /\ actual.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\
    abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule_all abi_builtin_encode_setup_none_execute >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK encoded` >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  drule_all abi_encoder_run_sequence_extend_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_encoder_extend_sim_sim >> strip_tac >>
  qexists_tac `encoded with vs_inst_idx := LENGTH ready.cs_current_insts` >>
  gvs[abi_builtin_allocation_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem abi_encode_method_setup_extend[local]:
  abi_builtin_encode_setup (SOME mid) maxlen st = (ops,ready) /\ fn_has_code st ready func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,32+32*word_size (maxlen+4))) /\
  32+32*word_size (maxlen+4) < dimword (:256) /\ p+32 < dimword (:256) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+36)) /\
    mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid /\
    fresh_vars_wrt limit_st actual /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id (32+32*word_size (maxlen+4)) p 32 initial actual /\
    actual.vs_current_bb = ready.cs_current_bb /\ actual.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\
    abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_encode_method_setup_sequence >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule_all abi_encoder_run_sequence_extend_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_encoder_extend_sim_sim >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  qexists_tac `actual with vs_inst_idx := LENGTH ready.cs_current_insts` >>
  gvs[abi_builtin_encode_setup_frame_def, abi_decode_frame_def,
    fresh_vars_wrt_def, eval_op_inst_idx] >> metis_tac[]
QED

Theorem abi_encode_window_setup_extend:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  fn_has_code st ready func /\
  mid_size = (case method_id of NONE => 0 | SOME mid => 4) /\
  write_size = (case method_id of NONE => 0 | SOME mid => 32) /\
  outsz = 32+32*word_size (maxlen+mid_size) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p+32 < dimword (:256) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_input ei at av sb cap initial.vs_memory /\
  (sb+cap <= p+32 \/ p+32+write_size <= sb) ==>
  ?actual.
    eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+32+mid_size)) /\
    fresh_vars_wrt limit_st actual /\
    FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,outsz) /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p write_size initial actual /\
    abi_encoder_input ei at av sb cap actual.vs_memory /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid) /\
    actual.vs_current_bb = ready.cs_current_bb /\
    actual.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\
    abi_encoder_extend_sim ctx func initial actual
Proof
  Cases_on `method_id` >> simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `mid_size = _` SUBST_ALL_TAC >>
  qpat_x_assum `write_size = _` SUBST_ALL_TAC >>
  qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
  rule_assum_tac (SRULE [])
  >- (drule abi_encode_setup_none_extend >> disch_then drule >>
      disch_then (qspecl_then [`p`, `limit_st`, `initial`, `ctx`] mp_tac) >>
      (impl_tac >- (pure_rewrite_tac[Q.SPECL [`32`, `32*word_size maxlen`] ADD_COMM] >>
        asm_rewrite_tac[])) >> strip_tac >>
      `abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id
         (32+32*word_size maxlen) p 0 initial actual` by
        gvs[abi_builtin_encode_setup_frame_def, abi_builtin_allocation_frame_def,
          abi_decode_frame_def] >>
      `FLOOKUP actual.vs_allocas st.cs_next_id =
         SOME (p,32+32*word_size maxlen)` by
        (irule abi_builtin_encode_setup_frame_row >> goal_assum (drule_at Any) >> simp[]) >>
      `abi_encoder_input ei at av sb cap actual.vs_memory` by
        (irule abi_builtin_encode_setup_frame_input >>
         goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
      qexists_tac `actual` >>
      pure_rewrite_tac[Q.SPECL [`32*word_size maxlen`, `32`] ADD_COMM] >> simp[]) >>
  drule abi_encode_method_setup_extend >> disch_then drule >>
  disch_then (qspecl_then [`p`, `limit_st`, `initial`, `ctx`] mp_tac) >>
  (impl_tac >- (pure_rewrite_tac[Q.SPECL [`32`, `32*word_size (maxlen+4)`] ADD_COMM] >>
    asm_rewrite_tac[])) >> strip_tac >>
  `FLOOKUP actual.vs_allocas st.cs_next_id =
     SOME (p,32+32*word_size (maxlen+4))` by
    (irule abi_builtin_encode_setup_frame_row >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_encoder_input ei at av sb cap actual.vs_memory` by
    (irule abi_builtin_encode_setup_frame_input >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  qexists_tac `actual` >>
  pure_rewrite_tac[Q.SPECL [`32*word_size (maxlen+4)`, `32`] ADD_COMM] >> simp[]
QED
