(* Static-element dynamic arrays (no clamp, not ABI-dynamic) decode by one
 * bulk copy; the complete paired decoder contract for that case. *)
Theory ctorDeployMemoryRunPtrPrefixCompleteBulk
Ancestors
  ctorDeployMemoryRunPtrPrefixCompleteCopy
  ctorDeployMemoryRunPtrPrefixCompleteCode
  ctorDeployLoweringEntryCompleteNoAlloc abiDecoderBulkReentry abiDecoderBulk
  ctorAbiActualBulk vyperTypeABI vyperABI abiDecoderCorrectPrimitiveArray
  ctorDeployMemoryRunPtrPrefixCopyRun ctorDeployMemoryRunPtrPrefixCopySupport
  ctorDeployLoweringEntryArrayFrame ctorDeployLoweringEntryCompleteScalar
  ctorDeployLoweringEntryAllocation ctorDeployLoweringEntryRegistration
  ctorAbiActualFrame ctorAbiActualObservations ctorAbiActualWorld ctorAbiActualAlloc
  abiDecoderContract abiDecoderTypedContract abiDecoderCoherence abiDecoderLoop
  abiDecoderReentry abiDecoderReentryPointer abiDecoderBulkExecute
  abiEncoderRegisteredEffect fragExec allocaFrontierBound allocaBudgetProps
  exprLowering exprLoweringProps emitHelper compileEnv venomInst venomState
  venomExecSemantics ptrDiscipline ptrSafeRun valueEncoding words list rich_list
  arithmetic finite_map pred_set

Theorem prefix_bulk_var_frame[local]:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\
  run_inst_seq (emitted_insts st st') s = OK t /\ not_fresh_at st x ==>
  lookup_var x t = lookup_var x s
Proof
  strip_tac >> irule ctor_actual_sequence_var_frame >>
  goal_assum (drule_at Any) >>
  drule_all prefix_bulk_sentinel_code >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  simp[mk_inst_def, is_terminator_def] >>
  gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_ADD]
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

Theorem prefix_bulk_complete_code_contract:
  ~(is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
  (^CshiftCode) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  disch_then (strip_assume_tac o SIMP_RULE bool_ss []) >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >> gnvs[Excl "enc_def"] >>
  `abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
    (ListV avs) (ArrayV (DynArrayV vs))` by fs[abi_decoder_metadata_def] >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var (Var dst) /\
   abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    (Cases_on `src` >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= initial.vs_alloca_next /\
   initial.vs_alloca_next < dimword (:256)` by
    (drule_all deploy_ctor_shifted_frontier_bound >> strip_tac >> decide_tac) >>
  `abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn))) (ListV avs) (ArrayV (DynArrayV vs))
    st st.cs_next_id src (Var dst) DLOAD (Lit 0w) sb d initial.vs_alloca_next 0
    (abi_decoder_prune_vars st.cs_next_var initial)` by
    (irule ctor_actual_bulk_empty_window_pre >>
     asm_simp_tac bool_ss [vyper_to_abi_type_def] >> goal_assum (drule_at Any)) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def]) >>
  qpat_x_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def]) >>
  gnvs[Excl "enc_def"] >>
  drule_all abi_decoder_bulk_reentry_sequence >> strip_tac >>
  suspend "package"
QED

Resume prefix_bulk_complete_code_contract[package]:
  rename1 `run_inst_seq (emitted_insts st st') initial = OK t` >>
  drule_all abi_decoder_bulk_pre_facts >>
  simp[abi_decode_load_def, abi_decode_source_def, abi_decoder_prune_vars_def,
    Excl "enc_def"] >> strip_tac >>
  `d < dimword (:256) /\
   d+32+LENGTH vs * type_memory_bytes ce ty < dimword (:256) /\
   d+32+LENGTH vs * type_memory_bytes ce ty <= b+sz` by decide_tac >>
  `b <= w2n (n2w d:bytes32) /\
   w2n (n2w d:bytes32)+32+LENGTH vs * type_memory_bytes ce ty <= b+sz` by
    (simp[w2n_n2w] >>
     qpat_x_assum `type_memory_bytes ce ty = _` SUBST_ALL_TAC >> decide_tac) >>
  `abi_decode_load DLOAD (n2w sb:bytes32) initial = n2w (LENGTH vs)` by
    fs[abi_decode_load_def, abi_decode_source_def] >>
  `w2n (n2w d:bytes32)+32+LENGTH vs * type_memory_bytes ce ty < dimword (:256)` by
    (simp[w2n_n2w] >>
     qpat_x_assum `type_memory_bytes ce ty = _` SUBST_ALL_TAC >> decide_tac) >>
  `LENGTH vs * type_memory_bytes ce ty < dimword (:256)` by decide_tac >>
  drule_all prefix_bulk_success_ghost >>
  disch_then (qspecl_then [`PG`,`Ddead`] strip_assume_tac) >>
  suspend "finish"
QED
Resume prefix_bulk_complete_code_contract[finish]:
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  `frag_exec ctx st st' (\s. s = initial)
    (\s. s = t with vs_inst_idx := LENGTH st'.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> asm_simp_tac bool_ss [] >> metis_tac[]) >>
  `abi_decode_sim ctx func initial
    (t with vs_inst_idx := LENGTH st'.cs_current_insts) /\
   ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb` by
    (drule abi_decode_sim_from_fragment >> disch_then drule >> simp[]) >>
  drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_scratch_free_effect >>
  disch_then (qspecl_then [`site`,`ctor_actual_sites func (frag_ids st st')`,`func`,`ctx`] strip_assume_tac) >>
  drule_all prefix_copy_canonical_dynarray_package >> strip_tac >>
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x initial` by
    (rpt strip_tac >> irule prefix_bulk_var_frame >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `!a. a < lo ==> read_byte a t.vs_memory = read_byte a initial.vs_memory` by
    (drule prefix_copy_low_frame >> disch_then (qspec_then `lo` mp_tac) >> simp[]) >>
  qexistsl [`t with vs_inst_idx := LENGTH st'.cs_current_insts`,`H`,`qt`,
    `range_bytes [(d,32+LENGTH vs * type_memory_size tv)]`] >>
  simp[SUBSET_REFL, op_taint_def, Excl "enc_def"] >>
  `t.vs_data_section = initial.vs_data_section /\
   t.vs_call_ctx = initial.vs_call_ctx` by fs[abi_decode_frame_def] >>
  simp[allocas_from_def, lookup_var_def, fresh_vars_wrt_def,
    ctor_actual_scratch_def, abi_encoder_registered_effect_def, Excl "enc_def"] >>
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
Finalise prefix_bulk_complete_code_contract
