(* Additive paired interface: allocation origin belongs to the semantic endpoint. *)
Theory ctorDeployMemoryRunPtrPrefixCanonicalFloor
Ancestors
  ctorDeployMemoryRunPtrPrefixAllocationFloor
  ctorDeployMemoryRunPtrPrefixScalar ctorDeployMemoryRunPtrPrefixCopy
  ctorDeployMemoryRunPtrPrefixScalarClamps ctorDeployMemoryRunPtrPrefixScalarPackage
  ctorDeployMemoryRunPtrPrefixScalarBool ctorDeployMemoryRunPtrPrefixCanonical
  ctorDeployMemoryRunPtrPrefixCopyRun ctorDeployMemoryRunPtrPrefixCopySupport
  ctorAbiActualLabelBytes ctorAbiActualBytes ctorAbiActualBulk
  ctorAbiActualObservations ctorAbiActualWorld ctorAbiActualFrame
  abiDecoderBytesTyped abiDecoderBytesFrame abiDecoderReentryPointer
  abiDecoderReentry abiDecoderCoherence abiDecoderLoop
  abiEncoderRegisteredEffect allocaBudgetProps venomMemDefs
  abiCanonicalBytes abiDecoderBytes abiDecoderBulkReentry abiDecoderBulk
  abiDecoderCorrectPrimitiveArray abiDecoderTypedContract exprLowering vyperABI
  abiDecoderBulkExecute instIdxIndep memLocDefs
  abiEncoder abiDecoderContract abiDecoderClampedWord compileEnv exprLoweringProps
  venomState venomInst venomExecSemantics ptrDiscipline ptrSafeRun
  fragExec finite_map list rich_list words pred_set allocaFrontierBound

val canonical_pair_floor = ``\ty tv.
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
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
 unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 FLOOKUP G dst = SOME (b,sz) /\ b <= d /\
 d + type_memory_bytes ce ty <= b+sz /\
 op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
 lo <= initial.vs_alloca_next ==>
 ?actual H qt B.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
    lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\
 FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\
 DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem =
                        mem_bytes_at a 1 actual.vs_memory) ==>
    val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
                           op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)``;

Theorem prefix_canonical_int_paired_floor:
  type_to_abi_dec_info sf ce ty = DecPrimWord (IntClamp bits signed) ==>
  (^canonical_pair_floor) ty tv
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  drule_all prefix_scalar_prepare >> strip_tac >>
  `d < dimword (:256)` by
    (drule_all alloca_frontier_inv_bound >> decide_tac) >>
  `compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
    (DecPrimWord (IntClamp bits signed)) st = ((),st')` by metis_tac[] >>
  `d+32 <= b+sz` by metis_tac[] >>
  `!v. src = Var v \/ dst = v ==> not_fresh_at st v` by metis_tac[] >>
  drule_all (SRULE [] (Q.INST
    [`left` |-> `F`, `n` |-> `(n2w (if signed then bits DIV 8-1 else bits)):bytes32`,
     `clamp` |-> `IntClamp bits signed`, `m` |-> `0`]
    (SPEC_ALL prefix_scalar_checked_ghost))) >>
  disch_then (qspecl_then [`PG`,`Ddead`] strip_assume_tac) >>
  qabbrev_tac `actual = t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  rule_assum_tac (PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all prefix_scalar_transport >> strip_tac >>
  drule_all prefix_scalar_support_package >> strip_tac >>
  `allocas_from lo actual /\ lo <= actual.vs_alloca_next` by
    (irule prefix_allocation_floor_frame >> qexists_tac `initial` >> simp[]) >>
  qexistsl [`actual`,`H`,`qt`,`range_bytes [(d,32)]`] >>
  asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  simp[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]
QED

Theorem prefix_canonical_bytes_paired_floor:
  type_to_abi_dec_info sf ce ty = DecPrimWord (BytesMClamp m) ==>
  (^canonical_pair_floor) ty tv
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  drule_all prefix_scalar_prepare >> strip_tac >>
  `d < dimword (:256)` by
    (drule_all alloca_frontier_inv_bound >> decide_tac) >>
  `compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
    (DecPrimWord (BytesMClamp m)) st = ((),st')` by metis_tac[] >>
  `d+32 <= b+sz` by metis_tac[] >>
  `!v. src = Var v \/ dst = v ==> not_fresh_at st v` by metis_tac[] >>
  drule_all (SRULE [] (Q.INST
    [`left` |-> `T`, `signed` |-> `F`, `n` |-> `(n2w (m*8)):bytes32`,
     `clamp` |-> `BytesMClamp m`, `bits` |-> `0`]
    (SPEC_ALL prefix_scalar_checked_ghost))) >>
  disch_then (qspecl_then [`PG`,`Ddead`] strip_assume_tac) >>
  qabbrev_tac `actual = t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  rule_assum_tac (PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all prefix_scalar_transport >> strip_tac >>
  drule_all prefix_scalar_support_package >> strip_tac >>
  `allocas_from lo actual /\ lo <= actual.vs_alloca_next` by
    (irule prefix_allocation_floor_frame >> qexists_tac `initial` >> simp[]) >>
  qexistsl [`actual`,`H`,`qt`,`range_bytes [(d,32)]`] >>
  asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  simp[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]
QED

Theorem prefix_canonical_bool_paired_floor:
  type_to_abi_dec_info sf ce ty = DecPrimWord BoolClamp ==>
  (^canonical_pair_floor) ty tv
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  drule_all prefix_scalar_prepare >> strip_tac >>
  `d < dimword (:256)` by
    (drule_all alloca_frontier_inv_bound >> decide_tac) >>
  `compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
    (DecPrimWord BoolClamp) st = ((),st')` by metis_tac[] >>
  `d+32 <= b+sz` by metis_tac[] >>
  drule_all prefix_scalar_bool_ghost >>
  disch_then (qspecl_then [`PG`,`Ddead`] strip_assume_tac) >>
  qabbrev_tac `actual = t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  rule_assum_tac (PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all prefix_scalar_transport >> strip_tac >>
  drule_all prefix_scalar_support_package >> strip_tac >>
  `allocas_from lo actual /\ lo <= actual.vs_alloca_next` by
    (irule prefix_allocation_floor_frame >> qexists_tac `initial` >> simp[]) >>
  qexistsl [`actual`,`H`,`qt`,`range_bytes [(d,32)]`] >>
  asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  simp[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]
QED

Theorem prefix_canonical_bytestring_paired_floor:
  type_to_abi_dec_info sf ce ty = DecBytestring n ==>
  (^canonical_pair_floor) ty tv
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `sb < dimword (:256) /\ d < dimword (:256) /\
   type_memory_bytes ce ty < dimword (:256)` by
    (drule_all alloca_frontier_inv_bound >> asm_simp_tac bool_ss [] >> decide_tac) >>
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

Resume prefix_canonical_bytestring_paired_floor[package]:
  markerLib.RESUME_TAC >>
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
  qabbrev_tac `actual = t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  rule_assum_tac (PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `abi_decode_sim ctx func initial
    (t with vs_inst_idx := LENGTH st'.cs_current_insts)` by metis_tac[] >>
  drule_all prefix_copy_transport >> strip_tac >>
  drule_all prefix_copy_capacity_package >> strip_tac >>
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
  `allocas_from lo actual /\ lo <= actual.vs_alloca_next` by
    (irule prefix_allocation_floor_frame >> qexists_tac `initial` >> simp[]) >>
  qexistsl [`actual`,`H`,`qt`,`range_bytes [(d,type_memory_bytes ce ty)]`] >>
  asm_rewrite_tac[SUBSET_REFL] >>
  conj_tac >- (qpat_x_assum `DISJOINT _ _` mp_tac >> simp[]) >>
  simp[op_taint_def] >> metis_tac[]
QED
Finalise prefix_canonical_bytestring_paired_floor

Theorem prefix_canonical_noclamp_paired_floor:
  type_to_abi_dec_info sf ce ty = DecPrimWord NoClamp ==>
  (^canonical_pair_floor) ty tv
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule prefix_canonical_noclamp_paired_allocations >>
  BETA_TAC >>
  disch_then (drule_all_then (qspecl_then [`Ddead`,`PG`] strip_assume_tac)) >>
  `allocas_from lo actual /\ lo <= actual.vs_alloca_next` by
    (irule prefix_allocation_floor_frame >> qexists `initial` >> asm_rewrite_tac[]) >>
  qexistsl [`actual`,`H`,`qt`,`B`] >> asm_rewrite_tac[]
QED

Theorem prefix_canonical_primitive_paired_floor:
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
  (^canonical_pair_floor) ty tv
Proof
  Cases_on `clamp`
  >- MATCH_ACCEPT_TAC prefix_canonical_noclamp_paired_floor
  >- MATCH_ACCEPT_TAC prefix_canonical_int_paired_floor
  >- MATCH_ACCEPT_TAC prefix_canonical_bytes_paired_floor
  >> MATCH_ACCEPT_TAC prefix_canonical_bool_paired_floor
QED

Theorem prefix_canonical_bulk_paired_floor:
  ~(is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
  (^canonical_pair_floor) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule prefix_canonical_bulk_paired_allocations >> BETA_TAC >>
  disch_then (drule_all_then (qspecl_then [`Ddead`,`PG`] strip_assume_tac)) >>
  `allocas_from lo actual /\ lo <= actual.vs_alloca_next` by
    (irule prefix_allocation_floor_frame >> qexists `initial` >> asm_rewrite_tac[]) >>
  qexistsl [`actual`,`H`,`qt`,`B`] >> asm_rewrite_tac[]
QED
