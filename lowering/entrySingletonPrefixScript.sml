(* Arbitrary-offset singleton address setup in its original containing function. *)
Theory entrySingletonPrefix
Ancestors
  entryWordPrefix abiValidSingletonReentry abiValidSingletonSetup
  abiDecoderTypedCompose abiDecoderReentry abiDecoderContract
  entrySinkExtraction fragExec abiEncoderObserver instIdxIndep exprLoweringProps
  venomExecSemantics venomState compileEnv abiDecoderDynamicLoopSetup list rich_list

Theorem decoder_valid_singleton_setup_local_prefix:
  abi_decode_singleton_setup dst src opc hi st = ((child_src,child_dst),st') /\
  abi_valid_singleton_setup_pre st src dst opc hi sb d offset
    (abi_decoder_prune_vars st.cs_next_var initial) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\ ~initial.vs_halted ==>
  ?actual. actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~actual.vs_halted /\
    eval_operand child_src actual = SOME (n2w (sb + offset)) /\
    eval_operand child_dst actual = SOME (n2w d) /\
    abi_decoder_operand_live st'.cs_next_var child_src /\
    abi_decoder_operand_live st'.cs_next_var child_dst /\
    fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    local_prefix ctx func (st'.cs_current_bb,LENGTH st'.cs_current_insts) initial actual
Proof
  strip_tac >> drule_all abi_valid_singleton_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') initial = OK reached` >>
  `abi_decode_source_opcode opc` by fs[abi_valid_singleton_setup_pre_def] >>
  drule_all abi_valid_singleton_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'` by
    (fs[IS_PREFIX_APPEND, emitted_insts_def] >> simp[DROP_LENGTH_APPEND]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `LENGTH st.cs_current_insts + LENGTH (emitted_insts st st') =
    LENGTH st'.cs_current_insts` by metis_tac[LENGTH_APPEND] >>
  `local_prefix ctx func (initial.vs_current_bb,
      initial.vs_inst_idx + LENGTH (emitted_insts st st')) initial
      (reached with vs_inst_idx := initial.vs_inst_idx + LENGTH (emitted_insts st st'))` by
    (irule decoder_sequence_local_prefix >> asm_rewrite_tac[] >>
     qexists_tac `bb` >> asm_rewrite_tac[]) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  qexists_tac `reached with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED
