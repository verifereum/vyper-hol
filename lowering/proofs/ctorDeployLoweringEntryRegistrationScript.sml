(* Boundary probes for constructor registration above the immutable region. *)
Theory ctorDeployLoweringEntryRegistration
Ancestors
  loweringStateRelDefs
  ctorRegisterArgs fragExec moduleLowering
  compileEnv exprLoweringProps abiDecoderLoop loweringHalt abiEncoderRegisteredEffect venomState
  ctorAbiActualLabelWord ctorAbiActualObservations ctorAbiActualWordRun
  ctorAbiActualNarrowWord ctorAbiActualWorld ctorAbiActualReentry
  abiDecoderReentry abiDecoderClampedWord abiDecoderWordTyped
  abiDecoderLayout abiDecoderCoherence abiDecoderVarExtend
  abiDecoderContract abiDecoderReentryPointer instIdxIndep
  allocaFrontierBound allocaBudgetProps
  venomExecSemantics venomMemDefs venomInst abiDecoderVarSequence valueEncoding
  words finite_map list

Theorem deploy_ctor_register_empty_frame:
  !ce off size st ce' st' ctx func scope initial.
    compile_register_constructor_args ce [] off size st = (ce',st') /\
    local_ptrs_rel func ce [scope] initial ==>
    ?actual.
      local_ptrs_rel func ce' [scope] actual /\
      abi_decode_sim ctx func initial actual /\
      abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
      actual.vs_alloca_next = initial.vs_alloca_next /\
      actual.vs_gas_readings = initial.vs_gas_readings /\
      actual.vs_code = initial.vs_code /\ actual.vs_labels = initial.vs_labels
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_register_constructor_args_def, comp_return_def] >>
  qexists `initial` >>
  simp[abi_decode_sim_refl, abi_encoder_registered_effect_refl]
QED

(* The first instruction of a nonempty registration.  Capacity is stated
   relative to the actual frontier, not to an unshifted unit budget. *)
Theorem deploy_ctor_register_alloc_frame:
  !n st buf sa ctx func initial.
    compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
    n < dimword (:256) /\ initial.vs_alloca_next + n < dimword (:256) /\
    FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\
    ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?actual.
      abi_decode_sim ctx func initial actual /\
      actual.vs_alloca_next = initial.vs_alloca_next + n /\
      actual.vs_gas_readings = initial.vs_gas_readings /\
      actual.vs_code = initial.vs_code /\ actual.vs_labels = initial.vs_labels /\
      ~actual.vs_halted /\ actual.vs_current_bb = sa.cs_current_bb /\
      actual.vs_inst_idx = LENGTH sa.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `raw = update_var (STRING #"%" (toString st.cs_next_var))
    (n2w initial.vs_alloca_next)
    (initial with <| vs_allocas := initial.vs_allocas |+
      (st.cs_next_id,(initial.vs_alloca_next,n));
      vs_alloca_next := initial.vs_alloca_next+n |>)` >>
  `frag_exec ctx st sa (\u. u = initial)
    (\u. u = raw with vs_inst_idx := LENGTH sa.cs_current_insts) (K F)` by
    (irule compile_alloc_buffer_fresh_frag >> qexistsl [`buf`, `n`] >>
     simp[Abbr `raw`]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  simp[] >> strip_tac >>
  qexists `raw with vs_inst_idx := LENGTH sa.cs_current_insts` >>
  simp[abi_decode_sim_def, Abbr `raw`, update_var_def] >>
  metis_tac[]
QED

Theorem deploy_ctor_decoder_step_observations:
  abi_decoder_reentry_opcode inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  t.vs_gas_readings = s.vs_gas_readings /\ t.vs_code = s.vs_code /\
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

Theorem deploy_ctor_decoder_sequence_observations:
  !code s t. EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) code /\
  run_inst_seq code s = OK t ==>
  t.vs_gas_readings = s.vs_gas_readings /\ t.vs_code = s.vs_code /\
  t.vs_labels = s.vs_labels
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_all deploy_ctor_decoder_step_observations >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem deploy_ctor_scalar_frame_fragment:
  compile_abi_decode_to_buf dst src DLOAD hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. val_in_memory tv v d t.vs_memory /\ fresh_vars_wrt limit_st t /\
      abi_decode_frame d 32 initial t /\
      (!op w. abi_decoder_operand_live st.cs_next_var op /\
        eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
      abi_encoder_registered_effect {} [(d,32)] initial t /\
      (alloca_inv t <=> alloca_inv initial) /\
      (alloca_frontier_inv ctx func site t <=> alloca_frontier_inv ctx func site initial) /\
      t.vs_labels = initial.vs_labels /\
      t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all ctor_actual_word_ceiling_sequence >> strip_tac >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_scratch_free_effect >>
  disch_then (qspecl_then [`site`, `{}`, `func`, `ctx`] assume_tac) >>
  qexists `actual` >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx,
    abi_encoder_registered_effect_def, alloca_inv_def, alloca_frontier_inv_def,
    remaining_alloca_budget_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED

Theorem deploy_ctor_scalar_shifted_credit_fragment:
  !base credit.
  compile_abi_decode_to_buf dst src DLOAD hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  initial.vs_alloca_next + credit < dimword (:256) /\ base <= initial.vs_alloca_next ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. val_in_memory tv v d t.vs_memory /\ fresh_vars_wrt limit_st t /\
      abi_decode_frame d 32 initial t /\
      (!op w. abi_decoder_operand_live st.cs_next_var op /\
        eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
      abi_encoder_registered_effect {} [(d,32)] initial t /\
      (alloca_inv t <=> alloca_inv initial) /\
      (alloca_frontier_inv ctx func site t <=> alloca_frontier_inv ctx func site initial) /\
      t.vs_labels = initial.vs_labels /\
      t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code /\
      t.vs_alloca_next + credit < dimword (:256) /\ base <= t.vs_alloca_next) (K F)
Proof
  rpt gen_tac >> strip_tac >> drule_all deploy_ctor_scalar_frame_fragment >>
  simp[frag_exec_def] >> rpt strip_tac >>
  first_x_assum drule_all >> simp[] >>
  disch_then (qspecl_then [`site`, `func`, `ctx`] strip_assume_tac) >>
  qexists `t` >> gvs[]
QED
