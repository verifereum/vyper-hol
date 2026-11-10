(* Primitive reentry transport, shared by scalar and bytestring outcomes. *)
Theory exprSimAbiDecodePrimitiveOwned
Ancestors
  loweringStateRelDefs
  exprSimAbiDecodeOwnedContext exprSimAbiDecodeMemberExecute exprSimAbiDecodeAbortReentry
  abiDecoderPrimitiveFetched abiDecoderBytestringOutcome abiDecoderWordOutcome
  abiDecoderReentry abiDecoderReentryPointer abiDecoderVarSequence abiDecoderVarExtend
  abiDecoderSiteEffect actualDecoderSites abiDecoderScalarOutcome abiDecoderContract
  abiDecoderBytestringSource abiDecoderCoherence exprLowering compileEnv vyperABI
  contractABI vyperValue abiDecoderFiniteControl abiDecoderSequenceReach
  abiDecoderBytes abiDecoderBytesTyped abiDecoderBytesPhases abiDecoderFrame
  abiDecoderClampedWord exprSimAbiDecodeSiteProvenance valueEncodingProps abiCanonicalHeadSize
  venomExecSemantics venomState venomInst exprLoweringProps list arithmetic valueEncodingProofs

Theorem abi_decode_primitive_abort_opcode[local]:
  abi_bytes_opcode inst.inst_opcode /\
  step_inst_base inst s = Abort a u ==> inst.inst_opcode = ASSERT /\ a = Revert_abort
Proof
  strip_tac >> fs[abi_bytes_opcode_def, abi_word_opcode_def] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_rewrite_tac [Once step_inst_base_def, opcode_case_def] >>
  simp_tac (srw_ss()) [exec_pure1_def, exec_pure2_def, exec_read1_def,
    exec_write2_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem abi_decode_primitive_sequence_vars_extend_abort:
  !insts extras s t u.
  EVERY (\i. abi_bytes_opcode i.inst_opcode) insts /\
  abi_decoder_vars_extend extras s t /\
  run_inst_seq insts s = Abort Revert_abort u ==>
  ?v. run_inst_seq insts t = Abort Revert_abort v
Proof
  Induct >- simp[run_inst_seq_def] >>
  qx_gen_tac `inst` >> rpt gen_tac >>
  simp_tac bool_ss [EVERY_DEF, run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base inst s` >> gvs[]
  >>~- ([`step_inst_base inst s = OK v`],
    `abi_decoder_reentry_opcode inst.inst_opcode` by
      fs[abi_bytes_opcode_def, abi_word_opcode_def, abi_decoder_reentry_opcode_def] >>
    drule_all abi_decoder_step_vars_extend >> strip_tac >>
    first_x_assum drule_all >> strip_tac >>
    simp[] >> metis_tac[]) >>
  `abi_bytes_opcode inst.inst_opcode` by simp[] >>
  drule_all abi_decode_primitive_abort_opcode >> strip_tac >>
  drule_all abi_decode_assert_vars_extend_abort >> strip_tac >>
  simp[] >> metis_tac[]
QED

Theorem abi_decode_primitive_reentry_effect:
  decode_site_effect ctx func next writes (abi_decoder_prune_vars floor s) clean /\
  abi_decoder_vars_extend extras clean actual /\ next <= floor /\
  (!op w. abi_decoder_operand_live floor op /\ eval_operand op s = SOME w ==>
    eval_operand op actual = SOME w) ==>
  decode_site_effect ctx func next writes s actual
Proof
  strip_tac >> drule abi_decoder_vars_extend_observations >> strip_tac >>
  drule abi_decoder_vars_extend_restore >> strip_tac >>
  `decode_site_resources ctx func actual` by
    (irule decode_site_resources_fields >> qexists `clean` >>
     fs[decode_site_effect_def, venom_state_component_equality]) >>
  `decode_static_frame s actual` by
    (drule abi_decoder_vars_extend_restore >>
     fs[decode_site_effect_def, decode_static_frame_def, abi_decoder_prune_vars_def,
       venom_state_component_equality]) >>
  fs[decode_site_effect_def, decode_memory_frame_def, abi_decoder_prune_vars_def] >>
  metis_tac[abi_decoder_operand_live_mono]
QED

Theorem abi_decode_scalar_source_reentry:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecPrimWord clamp) st = ((),st') /\
  eval_operand src s = SOME(n2w pos) /\ eval_operand base_op s = SOME(n2w B) /\
  eval_operand dst s = SOME(n2w d) /\ eval_operand hi s = SOME(n2w H) /\
  pos+32 <= H /\ B+H < dimword(:256) /\ d+32 < dimword(:256) /\
  EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op;hi] /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  next <= st.cs_next_var /\ abi_decoder_clamp_wf clamp /\
  decode_site_resources ctx func s /\ {a | d <= a /\ a < d+32} SUBSET writes /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  bs = mem_bytes_at (B+pos) 32 s.vs_memory ==>
  (?t v. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decode_source_accepts env ty bs v /\ val_in_memory tv v d t.vs_memory /\
    fresh_vars_wrt limit_st t /\ decode_site_effect ctx func next writes s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) \/
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
    ~(?v. abi_decode_source_accepts env ty bs v))
Proof
  strip_tac >> fs[EVERY_DEF] >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s)` by
    irule abi_decoder_prune_fresh >>
  `decode_site_resources ctx func (abi_decoder_prune_vars st.cs_next_var s)` by
    (irule decode_site_resources_fields >> qexists `s` >>
     simp[abi_decoder_prune_vars_def]) >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w pos) /\
   eval_operand base_op (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w B) /\
   eval_operand dst (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w d) /\
   eval_operand hi (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w H)` by
    asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `bs = mem_bytes_at (B+pos) 32
    (abi_decode_source MLOAD (abi_decoder_prune_vars st.cs_next_var s))` by
    simp[abi_decode_source_def, abi_decoder_prune_vars_def] >>
  drule_all abi_decoder_word_opcodes >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st') /\
   EVERY (\i. abi_bytes_opcode i.inst_opcode) (emitted_insts st st')` by
    (fs[EVERY_MEM, abi_word_opcode_def, abi_bytes_opcode_def,
       abi_decoder_reentry_opcode_def] >> metis_tac[]) >>
  drule_all abi_decoder_scalar_source_outcome >>
  disch_then (qspec_then `next` strip_assume_tac)
  >- (drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
      drule_all abi_decoder_vars_extend_observations >> strip_tac >>
      `decode_site_effect ctx func next writes s actual` by
        (drule_all abi_decode_primitive_reentry_effect >> simp[]) >>
      disj1_tac >> qexistsl_tac [`actual`, `v`] >>
      gvs[abi_decode_source_accepts_def, abi_decoder_prune_vars_def, abi_decode_source_def]) >>
  `abi_decoder_vars_extend s.vs_vars (abi_decoder_prune_vars st.cs_next_var s) s` by
    irule abi_decoder_prune_extension >>
  drule_all abi_decode_primitive_sequence_vars_extend_abort >> strip_tac >>
  disj2_tac >> gvs[abi_decoder_prune_vars_def] >>
  fs[abi_decode_source_accepts_def] >> metis_tac[]
QED

Theorem abi_decode_bytestring_source_reentry:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecBytestring n) st = ((),st') /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand src s = SOME(n2w pos) /\ eval_operand base_op s = SOME(n2w B) /\
  eval_operand dst s = SOME(n2w d) /\ eval_operand hi s = SOME(n2w H) /\
  pos < dimword(:256) /\ B+H < dimword(:256) /\
  d+abi_decode_bytes_copy_size n < dimword(:256) /\
  (B+H <= d \/ d+abi_decode_bytes_copy_size n <= B) /\
  EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op;hi] /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  next <= st.cs_next_var /\ decode_site_resources ctx func s /\
  {a | d <= a /\ a < d+abi_decode_bytes_copy_size n} SUBSET writes /\
  bs = mem_bytes_at (B+pos) (H-pos) s.vs_memory /\
  (bt = BytesT (Dynamic n) \/ bt = StringT n) ==>
  (?t v. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decode_source_accepts env (BaseT bt) bs v /\
    val_in_memory (BaseTV bt) v d t.vs_memory /\
    fresh_vars_wrt limit_st t /\ decode_site_effect ctx func next writes s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) \/
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
    ~(?v. abi_decode_source_accepts env (BaseT bt) bs v))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  simp_tac bool_ss [EVERY_DEF] >> strip_tac >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s)` by
    irule abi_decoder_prune_fresh >>
  `decode_site_resources ctx func (abi_decoder_prune_vars st.cs_next_var s)` by
    (irule decode_site_resources_fields >> qexists `s` >>
     simp[abi_decoder_prune_vars_def]) >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w pos) /\
   eval_operand base_op (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w B) /\
   eval_operand dst (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w d) /\
   eval_operand hi (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w H)` by
    asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `bs = mem_bytes_at (B+pos) (H-pos)
    (abi_decoder_prune_vars st.cs_next_var s).vs_memory` by
    simp[abi_decoder_prune_vars_def] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_opcodes >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')` by
    (fs[EVERY_MEM, abi_word_opcode_def, abi_bytes_opcode_def,
       abi_decoder_reentry_opcode_def] >> metis_tac[]) >>
  `w2n (abi_decode_load MLOAD (n2w (B+pos):bytes32)
     (abi_decoder_prune_vars st.cs_next_var s)) =
   w2n (abi_decode_load MLOAD (n2w (B+pos):bytes32)
     (abi_decoder_prune_vars st.cs_next_var s))` by simp[] >>
  drule_all abi_decoder_bytestring_source_outcome >>
  disch_then (qspecl_then [`next`, `env`] strip_assume_tac)
  >- (drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
      drule_all abi_decoder_vars_extend_observations >> strip_tac >>
      `decode_site_effect ctx func next writes s actual` by
        (drule_all abi_decode_primitive_reentry_effect >> simp[]) >>
      disj1_tac >> qexistsl_tac [`actual`, `v`] >>
      gvs[abi_decode_source_accepts_def, abi_decoder_prune_vars_def]) >>
  `abi_decoder_vars_extend s.vs_vars (abi_decoder_prune_vars st.cs_next_var s) s` by
    irule abi_decoder_prune_extension >>
  drule_all abi_decode_primitive_sequence_vars_extend_abort >> strip_tac >>
  disj2_tac >> gvs[abi_decoder_prune_vars_def] >>
  fs[abi_decode_source_accepts_def] >> metis_tac[]
QED

Theorem abi_decode_scalar_source_shape:
  assignable_type env ty /\ abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
  ~is_dynamic (vyper_to_abi_type env ty) /\
  static_length (vyper_to_abi_type env ty) = 32 /\ type_memory_bytes ce ty = 32
Proof
  strip_tac >> drule_all abi_decoder_primitive_is_word >> strip_tac >>
  Cases_on `ty` >> gvs[is_word_type_def]
  >- (Cases_on `b` >> gvs[is_word_type_def, vyper_to_abi_type_def,
       vyper_base_to_abi_type_def, is_dynamic_def, static_length_def,
       type_memory_bytes_def] >>
      Cases_on `b'` >> gvs[is_word_type_def, vyper_base_to_abi_type_def,
       is_dynamic_def, static_length_def, type_memory_bytes_def]) >>
  gvs[abi_decoder_coherent_flag_iff, vyper_to_abi_type_def,
      is_dynamic_def, static_length_def, type_memory_bytes_def]
QED

Theorem abi_decode_scalar_owned_contract:
  type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord clamp ==>
  abi_decode_owned_child_contract ce env ty tv
Proof
  strip_tac >> simp_tac bool_ss [abi_decode_owned_child_contract_def] >>
  rpt gen_tac >> strip_tac >>
  qhdtm_assum `abi_decode_context_pre` mp_tac >>
  simp_tac bool_ss [abi_decode_context_pre_def] >> strip_tac >>
  drule_all abi_decode_scalar_source_shape >> strip_tac >>
  drule_all abi_decoder_primitive_clamp_wf >> strip_tac >>
  `compile_abi_decode_to_buf dst src MLOAD base_op hi (DecPrimWord clamp) st = ((),last)` by
    metis_tac[] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_word_inst_extends >> strip_tac >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `abi_decode_source_view (vyper_to_abi_type env ty) bs pos =
    mem_bytes_at (B+pos) 32 s.vs_memory` by
    (simp[abi_decode_source_view_def, IgnAsm `bs = _`] >>
     qpat_x_assum `bs = mem_bytes_at _ _ _` SUBST1_TAC >>
     irule mem_bytes_at_window >> metis_tac[]) >>
  `EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op;hi]` by
    fs[EVERY_DEF] >>
  `pos+32 <= LENGTH bs /\ d+32 < dimword(:256)` by metis_tac[] >>
  `fn_has_code st last fn /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[abi_decode_code_context_def, abi_decode_entry_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st last)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `{a | d <= a /\ a < d+32} SUBSET
    (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce ty})` by
    simp[pred_setTheory.SUBSET_DEF] >>
  drule_all abi_decode_scalar_source_reentry >>
  strip_tac
  >- (drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
      simp_tac bool_ss [abi_decode_context_result_def] >> disj1_tac >>
      qexistsl_tac [`t'`, `v`] >>
      conj_tac >- metis_tac[Dreach_straight_prefix] >>
      gvs[abi_decode_entry_def, fresh_vars_wrt_def, decode_site_effect_inst_idx,
        abi_decode_alloc_progress_def, decode_site_effect_def, decode_static_frame_def] >>
      conj_tac >- (rpt strip_tac >> gvs[]) >>
      qpat_x_assum `(_ : venom_state) = _` mp_tac >>
      simp[venom_state_component_equality]) >>
  drule_all abi_decoder_run_sequence_abort >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  simp_tac bool_ss [abi_decode_context_result_def, Dabort_def] >> disj2_tac >>
  qexists `t with vs_inst_idx := n` >> conj_tac
  >- (qexists `0` >> asm_rewrite_tac[]) >> fs[vyper_to_abi_type_def]
QED

Theorem abi_decode_bytestring_owned_contract:
  (bt = BytesT (Dynamic n) \/ bt = StringT n) ==>
  abi_decode_owned_child_contract ce env (BaseT bt) (BaseTV bt)
Proof
  disch_then assume_tac >> simp_tac bool_ss [abi_decode_owned_child_contract_def] >>
  rpt gen_tac >> strip_tac >>
  qhdtm_assum `abi_decode_context_pre` mp_tac >>
  simp_tac bool_ss [abi_decode_context_pre_def] >> strip_tac >>
  `type_to_abi_dec_info ce.ce_struct_fields ce (BaseT bt) = DecBytestring n /\
   type_memory_bytes ce (BaseT bt) = abi_decode_bytes_copy_size n /\
   is_dynamic (vyper_to_abi_type env (BaseT bt))` by
    (fs[type_to_abi_dec_info_def, type_memory_bytes_def, abi_decode_bytes_copy_size_def,
        vyper_to_abi_type_def, vyper_base_to_abi_type_def, is_dynamic_def] >>
     simp[type_to_abi_dec_info_def, type_memory_bytes_def, abi_decode_bytes_copy_size_def,
        vyper_to_abi_type_def, vyper_base_to_abi_type_def, is_dynamic_def]) >>
  `compile_abi_decode_to_buf dst src MLOAD base_op hi (DecBytestring n) st = ((),last)` by
    metis_tac[] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `inst_extends st last` by (drule_all abi_decode_bytes_position_shape >> simp[]) >>
  `abi_decode_source_view (vyper_to_abi_type env (BaseT bt)) bs pos =
    mem_bytes_at (B+pos) (LENGTH bs-pos) s.vs_memory` by
    (simp[abi_decode_source_view_def, IgnAsm `bs = _`] >>
     qpat_x_assum `bs = mem_bytes_at _ _ _` SUBST1_TAC >>
     irule LIST_EQ >>
     simp_tac (srw_ss()) [LENGTH_DROP, LENGTH_mem_bytes_at] >>
     rpt strip_tac >>
     `pos + x < LENGTH bs /\ x + pos < LENGTH bs /\ pos <= LENGTH bs` by decide_tac >>
     asm_simp_tac (srw_ss()) [EL_DROP, EL_mem_bytes_at, LENGTH_mem_bytes_at, ADD_ASSOC] >>
     simp_tac (srw_ss()) [AC ADD_ASSOC ADD_COMM]) >>
  `EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op;hi]` by fs[EVERY_DEF] >>
  `d+abi_decode_bytes_copy_size n < dimword(:256)` by metis_tac[] >>
  qhdtm_assum `abi_footprint_disjoint` mp_tac >>
  qpat_assum `type_memory_bytes _ _ = _` (fn th =>
    simp_tac (srw_ss()) [abi_footprint_disjoint_def, th]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `{a | d <= a /\ a < d+abi_decode_bytes_copy_size n} SUBSET
    (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce (BaseT bt)})` by
    simp[pred_setTheory.SUBSET_DEF] >>
  `fn_has_code st last fn /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[abi_decode_code_context_def, abi_decode_entry_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st last)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all abi_decode_bytestring_source_reentry >>
  disch_then (qspec_then `env` strip_assume_tac)
  >- (drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
      simp_tac bool_ss [abi_decode_context_result_def] >> disj1_tac >>
      qexistsl_tac [`t'`, `v`] >>
      conj_tac >- metis_tac[Dreach_straight_prefix] >>
      gvs[abi_decode_entry_def, fresh_vars_wrt_def, decode_site_effect_inst_idx,
        abi_decode_alloc_progress_def, decode_site_effect_def, decode_static_frame_def] >>
      conj_tac >- (rpt strip_tac >> gvs[]) >>
      qpat_x_assum `(_ : venom_state) = _` mp_tac >>
      simp[venom_state_component_equality] >> rpt strip_tac >> gvs[]) >>
  drule_all abi_decoder_run_sequence_abort >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  simp_tac bool_ss [abi_decode_context_result_def, Dabort_def] >> disj2_tac >>
  qexists `t with vs_inst_idx := n'` >> conj_tac
  >- (qexists `0` >> asm_rewrite_tac[]) >> fs[vyper_to_abi_type_def]
QED

Theorem abi_decode_base_owned_contract:
  abi_decode_owned_child_contract ce env (BaseT bt) (BaseTV bt)
Proof
  Cases_on `bt`
  >- (irule abi_decode_scalar_owned_contract >> simp[type_to_abi_dec_info_def])
  >- (irule abi_decode_scalar_owned_contract >> simp[type_to_abi_dec_info_def])
  >- (irule abi_decode_scalar_owned_contract >> simp[type_to_abi_dec_info_def])
  >- (irule abi_decode_scalar_owned_contract >> simp[type_to_abi_dec_info_def])
  >- (irule abi_decode_bytestring_owned_contract >> metis_tac[])
  >- (Cases_on `b`
      >- (irule abi_decode_scalar_owned_contract >> simp[type_to_abi_dec_info_def]) >>
      irule abi_decode_bytestring_owned_contract >> metis_tac[]) >>
  irule abi_decode_scalar_owned_contract >> simp[type_to_abi_dec_info_def]
QED

Theorem abi_decode_flag_owned_contract:
  abi_decode_owned_child_contract ce env (FlagT name) (FlagTV k)
Proof
  irule abi_decode_scalar_owned_contract >> simp[type_to_abi_dec_info_def]
QED
