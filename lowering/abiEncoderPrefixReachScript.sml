(* Preserve a straight-line prefix's observations at its containing-function endpoint. *)
Theory abiEncoderPrefixReach
Ancestors
  abiEncoderSequence abiBuiltinPrefix abiDecoderReentryAddress abiDecoderDynamicLoopSetup
  abiDecoderReentry abiDecoderContract abiDecoderLoop fragExec instIdxIndep compileEnv
  emitHelperProps exprLoweringProps venomExecSemantics venomState venomInst words list

Theorem abi_encoder_prefix_reach:
  abi_builtin_prefix st st' limit_st initial encoded /\ eval_operand out encoded = SOME w /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st') /\
  fn_has_code st st' func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME w /\ fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED
