(* Observations of actual straight-line decoder endpoints. *)
Theory entryDecoderObservations
Ancestors
  abiDecoderValidBytes ctorAbiActualObservations abiDecoderVarSequence
  oracleExecProps venomExecSemantics venomState venomInst exprLoweringProps fragExec list

Theorem entry_decoder_step_gas_readings:
  abi_decoder_reentry_opcode inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  t.vs_gas_readings = s.vs_gas_readings
Proof
  strip_tac >> irule step_inst_base_gas_readings >>
  goal_assum (drule_at Any) >> gvs[abi_decoder_reentry_opcode_def]
QED

Theorem entry_decoder_sequence_gas_readings:
  !code s t. EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) code /\
  run_inst_seq code s = OK t ==> t.vs_gas_readings = s.vs_gas_readings
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_all entry_decoder_step_gas_readings >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem entry_decoder_valid_bytes_observations:
  compile_abi_decode_to_buf dst src opc (Lit 0w) hi (DecBytestring n) st = ((),st') /\
  abi_decoder_valid_bytes_pre n at bs payload st src dst opc (Lit 0w) hi 0 sb d s /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st') ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d t.vs_memory /\
    val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d t.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_gas_readings = s.vs_gas_readings /\ t.vs_labels = s.vs_labels
Proof
  strip_tac >> drule_all abi_decoder_valid_bytes_sequence >> strip_tac >>
  drule_all entry_decoder_sequence_gas_readings >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  qexists_tac `t` >> simp[]
QED
