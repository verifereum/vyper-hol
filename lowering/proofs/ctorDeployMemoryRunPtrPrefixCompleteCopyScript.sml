(* Exact frames for the concrete bytestring decoder sequence. *)
Theory ctorDeployMemoryRunPtrPrefixCompleteCopy
Ancestors
  loweringStateRelDefs valueEncodingDefs
  ctorDeployMemoryRunPtrPrefixCompleteCode ctorDeployMemoryRunPtrPrefixCanonicalFloor
  ctorDeployMemoryRunPtrPrefixCopy ctorDeployMemoryRunPtrPrefixCopySupport
  ctorDeployMemoryRunPtrPrefixCopyRun ctorDeployMemoryRunPtrPrefixCompleteScalar
  ctorDeployLoweringEntryAllocation ctorDeployLoweringEntryArrayFrame ctorDeployLoweringEntryCompleteScalar ctorDeployLoweringEntryRegistration
  fragExec abiCanonicalBytes abiDecoderBytes
  ctorAbiActualFrame ctorAbiActualBytes ctorAbiActualAlloc ctorAbiActualObservations ctorAbiActualWorld
  abiDecoderBytesFrame abiDecoderBytesTyped abiDecoderReentry abiDecoderReentryPointer
  abiDecoderContract abiDecoderTypedContract abiDecoderCoherence abiDecoderLoop
  abiEncoder abiEncoderRegisteredEffect allocaFrontierBound allocaBudgetProps
  exprLowering exprLoweringProps emitHelper compileEnv venomInst venomState venomExecSemantics
  ptrDiscipline ptrSafeRun valueEncoding words list rich_list arithmetic finite_map pred_set

Theorem prefix_bytes_outputs_fresh[local]:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) (DecBytestring n) st = ((),st') ==>
  EVERY (\i. EVERY (\x. ~not_fresh_at st x) i.inst_outputs)
    (emitted_insts st st')
Proof
  simp[compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
    emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, mk_inst_def, not_fresh_at_def] >>
  metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]
QED

Theorem prefix_bytes_var_frame:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) (DecBytestring n) st = ((),st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\ not_fresh_at st x ==>
  lookup_var x t = lookup_var x s
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  drule prefix_bytes_outputs_fresh >> strip_tac >>
  irule ctor_actual_sequence_var_frame >> goal_assum (drule_at Any) >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem prefix_copy_low_frame:
  abi_decode_frame d cap initial final /\ lo <= d ==>
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
  rewrite_tac[ONE, REPLICATE, HD]
QED

val CshiftCode = ``\ty tv.
 !dst src st st' ctx func site initial limit_st sb d D N ids av v root_di
  G tn b sz Ddead lo PG.
 compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
   (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\
 eval_operand (Var dst) initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
   initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (!x. src = Var x \/ Var dst = Var x \/ Lit 0w = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb.
    lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 FLOOKUP G dst = SOME (b,sz) /\ b <= d /\
 d + type_memory_bytes ce ty <= b+sz /\
 op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
 lo <= initial.vs_alloca_next /\ lo <= d ==>
 ?actual H qt B.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\ actual.vs_gas_readings = initial.vs_gas_readings /\
 (!a. a < lo ==> read_byte a actual.vs_memory = read_byte a initial.vs_memory) /\
 FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\
 DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
    val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
                           op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)``;

Theorem prefix_bytestring_complete_code_contract:
  type_to_abi_dec_info sf ce ty = DecBytestring n ==> (^CshiftCode) ty tv
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `sb < dimword (:256) /\ d < dimword (:256) /\
   type_memory_bytes ce ty < dimword (:256)` by
    (drule_all deploy_ctor_shifted_frontier_bound >> strip_tac >> decide_tac) >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var (Var dst) /\
   abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    (Cases_on `src` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
     (DecBytestring n) st = ((),st')` by metis_tac[] >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`hi` |-> `Lit (0w:bytes32)`]
      ctor_actual_bytestring_ceiling_sequence)) >> strip_tac >>
  suspend "package"
QED

Resume prefix_bytestring_complete_code_contract[package]:
  rename1 `run_inst_seq (emitted_insts st st') initial = OK t` >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `frag_exec ctx st st' (\s. s = initial)
    (\s. s = t with vs_inst_idx := LENGTH st'.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> asm_simp_tac bool_ss [] >> metis_tac[]) >>
  `abi_decode_sim ctx func initial
    (t with vs_inst_idx := LENGTH st'.cs_current_insts) /\
   ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb` by
    (drule abi_decode_sim_from_fragment >> disch_then drule >> simp[]) >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  drule_all ctor_actual_bytestring_metadata >> strip_tac >>
  `abi_decode_bytes_copy_size n < dimword (:256)` by metis_tac[] >>
  `n < dimword (:256)` by
    (`n+32 <= abi_decode_bytes_copy_size n` by simp[abi_decoder_bytes_copy_size] >>
     decide_tac) >>
  `abi_decode_load DLOAD (n2w sb:bytes32) initial = n2w (LENGTH bs)` by
    (irule canonical_bytes_count_load >>
     simp[abi_decode_source_def, Excl "enc_def"] >> metis_tac[]) >>
  `!x. src = Var x \/ dst = x ==> not_fresh_at st x` by metis_tac[] >>
  `b <= w2n (n2w d:bytes32) /\
   w2n (n2w d:bytes32) + abi_decode_bytes_copy_size n <= b+sz` by
    (simp[] >> metis_tac[]) >>
  drule_all prefix_bytestring_success_ghost >>
  disch_then (qspecl_then [`PG`,`Ddead`] strip_assume_tac) >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_scratch_free_effect >>
  disch_then (qspecl_then [`site`,`ctor_actual_sites func (frag_ids st st')`,`func`,`ctx`] strip_assume_tac) >>
  drule_all prefix_copy_capacity_package >> strip_tac >>
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x initial` by
    (rpt strip_tac >> irule prefix_bytes_var_frame >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `!a. a < lo ==> read_byte a t.vs_memory = read_byte a initial.vs_memory` by
    (drule prefix_copy_low_frame >> disch_then (qspec_then `lo` mp_tac) >> simp[]) >>
  qexistsl [`t with vs_inst_idx := LENGTH st'.cs_current_insts`,`H`,`qt`,
    `range_bytes [(d,type_memory_bytes ce ty)]`] >>
  simp[SUBSET_REFL, op_taint_def] >>
  `t.vs_data_section = initial.vs_data_section /\
   t.vs_call_ctx = initial.vs_call_ctx` by fs[abi_decode_frame_def] >>
  simp[allocas_from_def, lookup_var_def, fresh_vars_wrt_def,
    ctor_actual_scratch_def, abi_encoder_registered_effect_def] >>
  conj_tac >- fs[allocas_from_def] >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `abi_decode_frame _ _ initial t` mp_tac >>
    simp_tac bool_ss [abi_decode_frame_def] >> strip_tac >>
    first_x_assum irule >> decide_tac) >>
  conj_tac >- (irule deploy_ctor_alloca_frontier_fields >>
    goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (qpat_x_assum `ctor_actual_scratch func ids D N initial` mp_tac >>
    simp_tac bool_ss [ctor_actual_scratch_def]) >>
  conj_tac >- (qpat_x_assum `!x. not_fresh_at st x ==> lookup_var x t = _` mp_tac >>
    simp_tac bool_ss [lookup_var_def]) >>
  conj_tac >- (qpat_x_assum `fresh_vars_wrt limit_st t` mp_tac >>
    simp_tac bool_ss [fresh_vars_wrt_def]) >>
  qpat_x_assum `DISJOINT _ qt.t_mem` mp_tac >> simp[]
QED
Finalise prefix_bytestring_complete_code_contract
