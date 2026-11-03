(* Execution-derived label observations for canonical DLOAD decoding. *)
Theory ctorAbiActualObservations
Ancestors
  ctorAbiActualWorld ctorAbiActualReentry abiDecoderVarSequence
  abiDecoderReentry abiDecoderVarExtend
  venomExecSemantics venomState venomInst compileEnv exprLoweringProps
  finite_map list arithmetic

Theorem ctor_actual_step_labels:
  abi_decoder_reentry_opcode inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  t.vs_labels = s.vs_labels
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[abi_decoder_reentry_opcode_def] >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  pure_rewrite_tac[opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_read1_def, exec_write2_def,
    exec_alloca_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  simp[update_var_def, mstore_def, mcopy_def, write_memory_with_expansion_def,
    jump_to_def]
QED

Theorem ctor_actual_sequence_labels:
  !code s t. EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) code /\
  run_inst_seq code s = OK t ==> t.vs_labels = s.vs_labels
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_all ctor_actual_step_labels >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem ctor_actual_old_operand:
  t.vs_labels = s.vs_labels /\
  (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w) /\
  (!x. op = Var x ==> not_fresh_at st x) /\
  eval_operand op s = SOME w ==> eval_operand op t = SOME w
Proof
  strip_tac >> Cases_on `op` >> gvs[eval_operand_def] >>
  first_x_assum irule >> simp[]
QED

Theorem ctor_actual_prune_labels[simp]:
  (abi_decoder_prune_vars next s).vs_labels = s.vs_labels
Proof
  simp[abi_decoder_prune_vars_def]
QED

Theorem ctor_actual_extend_labels:
  abi_decoder_vars_extend extras clean actual ==>
  actual.vs_labels = clean.vs_labels
Proof
  metis_tac[abi_decoder_vars_extend_observations]
QED
