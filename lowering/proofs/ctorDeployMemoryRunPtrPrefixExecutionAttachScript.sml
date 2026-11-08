(* Attach ghosts to a supplied scalar execution, not a semantic existential. *)
Theory ctorDeployMemoryRunPtrPrefixExecutionAttach
Ancestors
  ctorDeployMemoryRunPtrPrefixScalarClamps
  ctorDeployLoweringEntryCompleteScalar abiDecoderReentryPointer
  abiDecoderClampedWord abiDecoderLoop abiDecoderReentry abiDecoderContract
  ptrSafeRun ptrDiscipline
  venomState venomExecSemantics words list

Theorem prefix_execution_int_attach:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
    (DecPrimWord (IntClamp bits signed)) st = ((),st') /\
  run_inst_seq (emitted_insts st st') initial = OK actual /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand (Var dst) initial = SOME (n2w d) /\ d < dimword (:256) /\
  (!v. src = Var v \/ Var dst = Var v \/ Lit 0w = Var v ==> not_fresh_at st v) /\
  fn_has_code st st' func /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= d /\ d+32 <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  allocas_from lo initial /\ ~ctx_has_dalloca ctx ==>
  ?H qt.
    actual.vs_outcomes = initial.vs_outcomes /\
    actual.vs_tx_ctx = initial.vs_tx_ctx /\
    actual.vs_block_ctx = initial.vs_block_ctx /\
    qt.t_mem = tn.t_mem DIFF range_bytes [(d,32)] /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==> FLOOKUP H v = FLOOKUP G v /\
      op_taint qt (Var v) = op_taint tn (Var v)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt
      (actual with vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  asm_rewrite_tac[] >>
  irule prefix_scalar_checked_ghost >>
  simp[] >> goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED
