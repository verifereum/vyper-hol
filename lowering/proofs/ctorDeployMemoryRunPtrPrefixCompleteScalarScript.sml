(* Canonical scalar execution producer at a single operational witness. *)
Theory ctorDeployMemoryRunPtrPrefixCompleteScalar
Ancestors
  loweringStateRelDefs valueEncodingDefs
  ctorDeployMemoryRunPtrPrefixChildShift
  ctorDeployMemoryRunPtrPrefixScalarPackage ctorDeployMemoryRunPtrPrefixScalarBool
  ctorAbiActualWordRun ctorAbiActualWorld ctorAbiActualObservations
  ctorDeployLoweringEntryCompleteScalar ctorDeployLoweringEntryRegistration
  abiDecoderReentryPointer abiDecoderReentry abiDecoderContract
  abiEncoderRegisteredEffect ctorAbiActualFrame compileEnv fragExec
  ctorDeployMemoryRunPtrPrefixCanonical ctorDeployMemoryRunPtrPrefixScalarClamps
  exprLoweringProps arithmetic abiEncoder emitHelper venomInst ctorAbiActualAlloc
  abiDecoderClampedWord valueEncoding ptrDiscipline allocaBudgetProps
  ctorDeployLoweringEntryAllocation venomMemDefs
  venomState venomExecSemantics words list

Theorem prefix_scalar_complete_execution:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w) (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand (Var dst) initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual.
    run_inst_seq (emitted_insts st st') initial = OK actual /\
    let final = actual with vs_inst_idx := LENGTH st'.cs_current_insts in
    val_in_memory tv v d final.vs_memory /\ fresh_vars_wrt limit_st final /\
    abi_decode_frame d 32 initial final /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op final = SOME w) /\
    final.vs_allocas = initial.vs_allocas /\
    final.vs_alloca_next = initial.vs_alloca_next /\
    final.vs_outcomes = initial.vs_outcomes /\
    final.vs_tx_ctx = initial.vs_tx_ctx /\ final.vs_block_ctx = initial.vs_block_ctx /\
    final.vs_gas_readings = initial.vs_gas_readings /\
    abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
      [(d,32)] initial final
Proof
  strip_tac >>
  drule_all ctor_actual_word_ceiling_sequence >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_scratch_free_effect >>
  disch_then (qspecl_then [`site`,`ctor_actual_sites func (frag_ids st st')`,`func`,`ctx`] strip_assume_tac) >>
  qexists `actual` >>
  gvs[LET_THM, fresh_vars_wrt_def, abi_decode_frame_def,
      instIdxIndepTheory.eval_op_inst_idx, abi_encoder_registered_effect_def] >>
  metis_tac[]
QED

Theorem prefix_scalar_noclamp_ghost:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
    (DecPrimWord NoClamp) st = ((),st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand (Var dst) s = SOME (n2w d) /\ d < dimword (:256) /\
  (!v. src = Var v \/ Var dst = Var v \/ Lit 0w = Var v ==> not_fresh_at st v) /\
  fn_has_code st st' fn /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= d /\ d+32 <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?H qt.
    qt.t_mem = tn.t_mem DIFF range_bytes [(d,32)] /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==> FLOOKUP H v = FLOOKUP G v /\
      op_taint qt (Var v) = op_taint tn (Var v)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt
      (t with vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule prefix_canonical_noclamp_shape >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[emitted_insts_def, rich_listTheory.IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND, APPEND] >>
     metis_tac[]) >>
  qabbrev_tac `x = "%" ++ toString st.cs_next_var` >>
  `x <> dst` by gvs[Abbr `x`, not_fresh_at_def] >>
  `x = "%" ++ toString st.cs_next_var` by simp[Abbr `x`] >>
  `b <= w2n (n2w d:bytes32) /\ w2n (n2w d:bytes32)+32 <= b+sz` by simp[w2n_n2w] >>
  drule_all prefix_canonical_noclamp_continuation >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qpat_assum `eval_operand src s = _`
    (mp_then Any mp_tac
      (INST_TYPE [alpha |-> ``:num # num``] prefix_canonical_noclamp_ghost_frame)) >>
  disch_then (drule_at (Pat `eval_operand (Var dst) s = _`)) >>
  disch_then (qspec_then `x` mp_tac) >>
  disch_then (qspec_then `tn` mp_tac) >>
  disch_then (qspec_then `st.cs_next_id` mp_tac) >>
  disch_then (qspec_then `G` mp_tac) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq (emitted_insts st st') s = OK endpoint` >>
  `t = endpoint` by metis_tac[exec_result_11] >>
  qmatch_asmsub_abbrev_tac `ghost.t_mem = _` >>
  qexistsl [`DRESTRICT G (COMPL {x})`,`ghost`] >>
  `w2n (n2w d:bytes32) = d` by simp[w2n_n2w] >>
  `LENGTH st'.cs_current_insts = s.vs_inst_idx + 2` by
    (qpat_x_assum `st'.cs_current_insts = _` mp_tac >>
     qpat_x_assum `s.vs_inst_idx = _` mp_tac >>
     simp[NoAsms]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> disch_tac >>
  `v <> x` by
    (qpat_x_assum `not_fresh_at st v` mp_tac >>
     simp[NoAsms, not_fresh_at_def, Abbr `x`] >>
     strip_tac >> first_x_assum irule >> simp[]) >>
  conj_tac >> first_assum irule >> asm_rewrite_tac[]
QED

Theorem prefix_scalar_complete_ghost:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
    (DecPrimWord clamp) st = ((),st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand (Var dst) s = SOME (n2w d) /\ d < dimword (:256) /\
  (!v. src = Var v \/ Var dst = Var v \/ Lit 0w = Var v ==> not_fresh_at st v) /\
  fn_has_code st st' fn /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= d /\ d+32 <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?H qt.
    qt.t_mem = tn.t_mem DIFF range_bytes [(d,32)] /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==> FLOOKUP H v = FLOOKUP G v /\
      op_taint qt (Var v) = op_taint tn (Var v)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt
      (t with vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> Cases_on `clamp`
  >- (irule prefix_scalar_noclamp_ghost >> goal_assum (drule_at Any) >> metis_tac[])
  >- (irule prefix_scalar_checked_ghost >> simp[] >>
      goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
      simp[] >> metis_tac[])
  >- (irule prefix_scalar_checked_ghost >> simp[] >>
      goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
      simp[] >> metis_tac[])
  >> irule prefix_scalar_bool_ghost >> goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem prefix_scalar_outputs_fresh[local]:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') ==>
  EVERY (\i. EVERY (\x. ~not_fresh_at st x) i.inst_outputs)
    (emitted_insts st st')
Proof
  Cases_on `clamp` >>
  FIRST [rename1 `IntClamp bits signed` >> Cases_on `signed`, all_tac] >>
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, compile_abi_decode_static_def,
       compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, not_fresh_at_def] >>
  metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]
QED

Theorem prefix_scalar_var_frame:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\ not_fresh_at st x ==>
  lookup_var x t = lookup_var x s
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  drule prefix_scalar_outputs_fresh >> strip_tac >>
  irule ctor_actual_sequence_var_frame >> goal_assum (drule_at Any) >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem prefix_scalar_low_frame:
  abi_decode_frame d 32 initial final /\ lo <= d ==>
  !a. a < lo ==> read_byte a final.vs_memory = read_byte a initial.vs_memory
Proof
  simp[abi_decode_frame_def] >> strip_tac >> rpt strip_tac >>
  `mem_bytes_at a 1 final.vs_memory = mem_bytes_at a 1 initial.vs_memory` by
    (first_x_assum irule >> decide_tac) >>
  pop_assum (mp_tac o AP_TERM ``HD : byte list -> byte``) >>
  simp[NoAsms, mem_bytes_at_def, codegenRelTheory.read_byte_def, HD_TAKE] >>
  once_rewrite_tac[GSYM (CONJUNCT1 EL)] >>
  simp[NoAsms, EL_APPEND_EQN, EL_DROP] >>
  simp[NoAsms, DECIDE ``0 < n-a <=> a<n``] >>
  rewrite_tac[ONE, rich_listTheory.REPLICATE, HD]
QED

Theorem prefix_scalar_complete_shift:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w) (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand (Var dst) initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= d /\ d+32 <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  allocas_from lo initial /\ ~ctx_has_dalloca ctx /\ lo <= d /\
  lo <= initial.vs_alloca_next /\ alloca_inv initial /\
  alloca_frontier_inv_from k ctx func site initial /\
  ctor_actual_scratch func ids scratch_base N initial /\
  scratch_base+N <= initial.vs_alloca_next ==>
  ?actual H qt.
    run_inst_seq (emitted_insts st st') initial = OK actual /\
    let final = actual with vs_inst_idx := LENGTH st'.cs_current_insts in
    val_in_memory tv v d final.vs_memory /\ fresh_vars_wrt limit_st final /\
    abi_decode_frame d 32 initial final /\
    abi_decode_sim ctx func initial final /\
    ~final.vs_halted /\ final.vs_current_bb = st'.cs_current_bb /\
    final.vs_inst_idx = LENGTH st'.cs_current_insts /\
    final.vs_data_section = initial.vs_data_section /\
    final.vs_call_ctx = initial.vs_call_ctx /\ final.vs_labels = initial.vs_labels /\
    final.vs_outcomes = initial.vs_outcomes /\
    final.vs_tx_ctx = initial.vs_tx_ctx /\ final.vs_block_ctx = initial.vs_block_ctx /\
    final.vs_gas_readings = initial.vs_gas_readings /\
    final.vs_allocas = initial.vs_allocas /\
    final.vs_alloca_next = initial.vs_alloca_next /\
    allocas_from lo final /\ lo <= final.vs_alloca_next /\
    alloca_inv final /\ alloca_frontier_inv_from k ctx func site' final /\
    ctor_actual_scratch func ids scratch_base N final /\
    scratch_base+N <= final.vs_alloca_next /\
    (!a. a < lo ==> read_byte a final.vs_memory = read_byte a initial.vs_memory) /\
    qt.t_mem = tn.t_mem DIFF range_bytes [(d,32)] /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x final = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint qt (Var x) = op_taint tn (Var x)) /\
    abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
      [(d,32)] initial final /\
    (?B. FINITE B /\ B SUBSET range_bytes [(d,32)] /\ DISJOINT B qt.t_mem /\
      (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 final.vs_memory) ==>
        val_in_memory tv v d mem)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt final) ==>
     !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
  strip_tac >>
  drule_all prefix_scalar_complete_execution >>
  disch_then (qspec_then `func` mp_tac) >>
  simp[LET_THM] >> strip_tac >>
  `!x. src = Var x \/ Var dst = Var x \/ Lit 0w = Var x ==> not_fresh_at st x` by
    (rpt strip_tac >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  drule_all prefix_scalar_complete_ghost >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all prefix_scalar_sim >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  `actual.vs_call_ctx = initial.vs_call_ctx /\
   actual.vs_data_section = initial.vs_data_section` by gvs[abi_decode_frame_def] >>
  qexistsl [`actual`,`H`,`qt`] >>
  simp[LET_THM] >>
  conj_tac >-
    (qpat_x_assum `allocas_from lo initial` mp_tac >> simp[allocas_from_def]) >>
  conj_tac >-
    (qpat_x_assum `alloca_inv initial` mp_tac >>
     simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]) >>
  conj_tac >-
    (irule deploy_ctor_alloca_frontier_fields >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >-
    (qpat_x_assum `ctor_actual_scratch func ids scratch_base N initial` mp_tac >>
     simp[ctor_actual_scratch_def]) >>
  conj_tac >-
    (drule prefix_scalar_low_frame >> simp[] >> metis_tac[]) >>
  conj_tac >-
    (rpt strip_tac >> simp[lookup_var_def] >>
     irule (SRULE [lookup_var_def] prefix_scalar_var_frame) >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  qexists `range_bytes [(d,32)]` >> simp[] >>
  conj_tac >- (drule_all prefix_scalar_support_package >> simp[]) >>
  conj_tac >- SET_TAC[] >>
  rpt strip_tac >> drule_all prefix_scalar_support >> simp[]
QED
