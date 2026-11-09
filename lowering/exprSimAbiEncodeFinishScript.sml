Theory exprSimAbiEncodeFinish
Ancestors
  abiBuiltinEncodeCorrect abiBuiltinEncodeCode abiEncoderSequence
  abiEncoderRegisteredEffect abiDecoderReentry abiDecoderDynamicLoopSetup
  abiEncoderWrites abiEncoderWindowLookup emitHelperProps exprLoweringProps
  abiDecoderContract abiDecoderFrameCompose instIdxIndep
  abiDecoderArrayHeader venomMemProps abiDecoderGuards abiDecoderRange
  emitHelper compileEnv venomState venomExecSemantics venomInst words list finite_map

Theorem abi_encode_store_run_open[local]:
  emit_void MSTORE [buf;value_op] st = ((),final) /\
  eval_operand buf s = SOME (n2w p) /\ eval_operand value_op s = SOME w /\
  p < dimword (:256) ==>
  run_inst_seq (emitted_insts st final) s = OK (mstore p w s)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  asm_simp_tac (srw_ss()) [run_inst_seq_def, Once step_inst_base_def,
    exec_write2_def, mk_inst_def, w2n_n2w]
QED

Theorem abi_encode_add_run_open[local]:
  emit_op ADD [lhs;rhs] st = (out,en) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b ==>
  out = Var ("%" ++ toString st.cs_next_var) /\
  run_inst_seq (emitted_insts st en) s =
    OK (update_var ("%" ++ toString st.cs_next_var) (a+b) s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  asm_simp_tac (srw_ss()) [run_inst_seq_def, Once step_inst_base_def,
    exec_pure2_def, bind_outputs_def, mk_inst_def]
QED
Theorem abi_encode_live_update_open[local]:
  abi_decoder_operand_live next op ==>
  eval_operand op (update_var (STRING #"%" (toString next)) w s) = eval_operand op s
Proof
  Cases_on `op` >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED


Theorem abi_encode_finish_sequence_open:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) /\
  eval_operand buf initial = SOME (n2w p) /\
  eval_operand encoded_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var buf /\ p < dimword (:256) ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    mload p actual = n2w (len+mid_size) /\
    abi_decode_frame p 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_labels = initial.vs_labels /\
    actual.vs_halted = initial.vs_halted /\
    actual.vs_accounts = initial.vs_accounts /\
    actual.vs_transient = initial.vs_transient /\
    actual.vs_logs = initial.vs_logs /\
    actual.vs_requests = initial.vs_requests /\
    actual.vs_pending_deletions = initial.vs_pending_deletions /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  Cases_on `mid_size > 0`
  >- (asm_simp_tac bool_ss [abi_builtin_encode_finish_def, comp_bind_def, LET_THM] >>
      pairarg_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> gvs[] >>
      rename1 `emit_op ADD [encoded_len;Lit (n2w mid_size)] st = (total_op,prepared_st)` >>
      `eval_operand (Lit (n2w mid_size)) initial = SOME (n2w mid_size)` by
        simp[eval_operand_def] >>
      drule_all abi_encode_add_run_open >> strip_tac >>
      qmatch_asmsub_abbrev_tac `OK prepared` >>
      `eval_operand buf prepared = SOME (n2w p) /\
       eval_operand total_op prepared = SOME (n2w (len+mid_size))` by
        (conj_tac
         >- (simp[Abbr `prepared`] >>
             pure_rewrite_tac[stringTheory.STRCAT, APPEND] >>
             simp[abi_encode_live_update_open]) >>
         simp[Abbr `prepared`, word_add_n2w,
           eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
      drule_all abi_encode_store_run_open >> strip_tac >>
      `run_inst_seq (emitted_insts st final) initial =
        OK (mstore p (n2w (len+mid_size)) prepared)` by
        (irule (cj 1 abi_decode_sequence_chain) >>
         goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
         metis_tac[inst_extends_emit_op, inst_extends_emit_void]) >>
      qexists `mstore p (n2w (len+mid_size)) prepared` >>
      simp[abi_decode_mstore_frame, mload_mstore_same, eval_operand_mstore] >>
      conj_tac
      >- (irule abi_decode_frame_trans >> qexists `prepared` >>
          simp[abi_decode_mstore_frame, Abbr `prepared`,
            abi_decode_frame_def, update_var_def]) >>
      conj_tac >- simp[Abbr `prepared`, update_var_def] >>
      conj_tac >- simp[Abbr `prepared`, update_var_def] >>
      conj_tac >- simp[Abbr `prepared`, update_var_def] >>
      conj_tac >- simp[Abbr `prepared`, update_var_def] >>
      ntac 5 (conj_tac >- simp[Abbr `prepared`, update_var_def, mstore_def]) >>
      rpt strip_tac >>
      simp[Abbr `prepared`] >>
      pure_rewrite_tac[stringTheory.STRCAT, APPEND] >>
      simp[abi_encode_live_update_open]) >>
  `mid_size = 0` by decide_tac >> gvs[abi_builtin_encode_finish_def] >> strip_tac >>
  drule_all abi_encode_store_run_open >> strip_tac >>
  qexists `mstore p (n2w len) initial` >>
  simp[abi_decode_mstore_frame, mload_mstore_same, eval_operand_mstore,
    mstore_def]
QED

Theorem abi_encode_finish_reach_open:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) /\ fn_has_code st final func /\
  eval_operand buf initial = SOME (n2w p) /\ eval_operand encoded_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var buf /\ p < dimword (:256) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\ mload p actual = n2w (len+mid_size) /\
    abi_decode_frame p 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\
    actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect {} [(p,32)] initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  drule_all abi_encode_finish_sequence_open >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK encoded` >>
  `eval_operand buf encoded = SOME (n2w p)` by
    (first_x_assum irule >> simp[]) >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists `encoded with vs_inst_idx := LENGTH final.cs_current_insts` >>
  gvs[abi_decode_frame_def, eval_op_inst_idx, mload_def,
    abi_encoder_registered_effect_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED
