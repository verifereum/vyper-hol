(* Canonical copy decoder endpoints: concrete execution and ghost pairing. *)
Theory ctorDeployMemoryRunPtrPrefixCopy
Ancestors
  loweringStateRelDefs
  ctorDeployMemoryRunPtrPrefixCanonical ctorDeployMemoryRunPtrPrefixCopyRun
  ctorDeployMemoryRunPtrPrefixCopySupport ctorAbiActualLabelBytes
  ctorAbiActualBytes ctorAbiActualObservations ctorAbiActualWorld
  abiDecoderBytesTyped abiDecoderBytesFrame abiDecoderReentryPointer
  abiDecoderReentry abiDecoderContract abiDecoderCoherence abiDecoderLoop
  abiEncoderRegisteredEffect allocaFrontierBound allocaBudgetProps
  ctorAbiActualFrame venomMemDefs abiCanonicalBytes abiDecoderBytes
  abiEncoder pred_set ctorAbiActualBulk abiDecoderBulkReentry abiDecoderBulk
  abiDecoderCorrectPrimitiveArray abiDecoderTypedContract exprLowering vyperABI
  abiDecoderBulkExecute
  fragExec instIdxIndep venomState venomInst venomExecSemantics compileEnv
  exprLoweringProps memLocDefs ptrDiscipline ptrSafeRun words list finite_map

Theorem prefix_copy_bytes_sim[local]:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) (Lit 0w)
    (DecBytestring n) st = ((),st') /\
  run_inst_seq (emitted_insts st st') initial = OK t /\
  fn_has_code st st' func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_decode_sim ctx func initial
    (t with vs_inst_idx := LENGTH st'.cs_current_insts) /\
  ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `frag_exec ctx st st' (\s. s = initial)
     (\s. s = t with vs_inst_idx := LENGTH st'.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[] >> gvs[EVERY_CONJ]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[]
QED

(* Common endpoint transport: the caller supplies the simulation of this very
   sequence, so semantic and ghost consumers cannot choose different states. *)
Theorem prefix_copy_transport:
  run_inst_seq (emitted_insts st st') initial = OK t /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st') /\
  abi_decode_sim ctx func initial
    (t with vs_inst_idx := LENGTH st'.cs_current_insts) /\
  ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
  val_in_memory tv v d t.vs_memory /\ fresh_vars_wrt limit_st t /\
  abi_decode_frame d cap initial t /\
  (!op w. abi_decoder_operand_live st.cs_next_var op /\
    eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
  t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
  alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
  ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
  actual = (t with vs_inst_idx := LENGTH st'.cs_current_insts) ==>
  val_in_memory tv v d actual.vs_memory /\
  abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
    [(d,cap)] initial actual /\
  alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
  ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
  actual.vs_data_section = initial.vs_data_section /\
  actual.vs_call_ctx = initial.vs_call_ctx /\
  (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
    lookup_var x actual = SOME w) /\
  ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
  actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
  abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
  actual.vs_labels = initial.vs_labels
Proof
  strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  drule_all ctor_actual_scratch_free_effect >>
  disch_then (qspecl_then [`site`, `ctor_actual_sites func (frag_ids st st')`, `func`, `ctx`] strip_assume_tac) >>
  `ctor_actual_scratch func ids D N t` by
    (gvs[ctor_actual_scratch_def] >> metis_tac[]) >>
  qpat_x_assum `actual = _` SUBST_ALL_TAC >>
  asm_simp_tac bool_ss [venom_state_accfupds] >>
  conj_tac >- (qpat_x_assum `abi_encoder_registered_effect _ _ _ _` mp_tac >>
    simp[NoAsms, abi_encoder_registered_effect_def] >> metis_tac[]) >>
  conj_tac >- (`alloca_inv t` by metis_tac[] >> pop_assum mp_tac >>
    simp[NoAsms, alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]) >>
  conj_tac >- (`alloca_frontier_inv ctx func site t` by metis_tac[] >>
    pop_assum mp_tac >>
    simp[NoAsms, alloca_frontier_inv_def, remaining_alloca_budget_def]) >>
  conj_tac >- (qpat_x_assum `ctor_actual_scratch func ids D N t` mp_tac >>
    simp[NoAsms, ctor_actual_scratch_def]) >>
  `t.vs_data_section = initial.vs_data_section /\
   t.vs_call_ctx = initial.vs_call_ctx` by gvs[abi_decode_frame_def] >>
  asm_rewrite_tac[] >>
  reverse conj_tac >- (qpat_x_assum `fresh_vars_wrt limit_st t` mp_tac >>
    simp[NoAsms, fresh_vars_wrt_def]) >>
  rpt gen_tac >> strip_tac >>
  `abi_decoder_operand_live st.cs_next_var (Var x)` by
    (simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  first_x_assum (qspec_then `Var x` mp_tac) >>
  simp[eval_operand_def, lookup_var_def]
QED

Theorem prefix_copy_bytes_prepare[local]:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),st') /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand (Var dst) initial = SOME (n2w d) /\
  sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
    initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  (!x. src = Var x \/ Var dst = Var x \/ Lit 0w = Var x ==> not_fresh_at st x) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  alloca_frontier_inv ctx func site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next ==>
  ?t. run_inst_seq (emitted_insts st st') initial = OK t /\
    val_in_memory tv v d t.vs_memory /\ fresh_vars_wrt limit_st t /\
    abi_decode_frame d (type_memory_bytes ce ty) initial t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next
Proof
  strip_tac >>
  `sb < dimword (:256) /\ d < dimword (:256) /\
   type_memory_bytes ce ty < dimword (:256)` by
    (drule_all alloca_frontier_inv_bound >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var (Var dst) /\
   abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    (Cases_on `src` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
     (DecBytestring n) st = ((),st')` by metis_tac[] >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`hi` |-> `Lit (0w:bytes32)`]
      ctor_actual_bytestring_ceiling_sequence)) >>
  strip_tac >> goal_assum (drule_at Any) >> simp[]
QED

val canonical_pair = ``\ty tv.
 !dst src st st' ctx func site initial limit_st sb d D N ids av v root_di
  G tn b sz Ddead lo PG.
 compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
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
 allocas_from lo initial /\ ~ctx_has_dalloca ctx ==>
 ?actual H qt B.
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

Theorem prefix_canonical_bytestring_paired:
  type_to_abi_dec_info sf ce ty = DecBytestring n ==>
  (^canonical_pair) ty tv
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all prefix_copy_bytes_prepare >> strip_tac >>
  `compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
     (DecBytestring n) st = ((),st')` by metis_tac[] >>
  drule_all prefix_copy_bytes_sim >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  qabbrev_tac `actual = t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  rule_assum_tac (PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `abi_decode_sim ctx func initial
    (t with vs_inst_idx := LENGTH st'.cs_current_insts)` by metis_tac[] >>
  drule_all prefix_copy_transport >> strip_tac >>
  drule_all prefix_copy_capacity_package >> strip_tac >>
  drule_all ctor_actual_bytestring_metadata >> strip_tac >>
  `sb < dimword (:256) /\ d < dimword (:256) /\
   abi_decode_bytes_copy_size n < dimword (:256)` by
    (drule_all alloca_frontier_inv_bound >>
     asm_simp_tac (srw_ss()) [] >> decide_tac) >>
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
  qexistsl [`actual`,`H`,`qt`,`range_bytes [(d,type_memory_bytes ce ty)]`] >>
  asm_rewrite_tac[SUBSET_REFL] >>
  conj_tac >- (qpat_x_assum `DISJOINT _ _` mp_tac >> simp[]) >>
  simp[op_taint_def] >> metis_tac[]
QED

Theorem prefix_copy_bulk_sim[local]:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\
  run_inst_seq (emitted_insts st st') initial = OK t /\
  fn_has_code st st' func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_decode_sim ctx func initial
    (t with vs_inst_idx := LENGTH st'.cs_current_insts) /\
  ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  `frag_exec ctx st st' (\s. s = initial)
     (\s. s = t with vs_inst_idx := LENGTH st'.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[] >> gvs[EVERY_CONJ]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[]
QED

val canonical_pair_allocations = ``\ty tv.
 !dst src st st' ctx func site initial limit_st sb d D N ids av v root_di
  G tn b sz Ddead lo PG.
 compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
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
 allocas_from lo initial /\ ~ctx_has_dalloca ctx ==>
 ?actual H qt B.
 actual.vs_allocas = initial.vs_allocas /\
 actual.vs_alloca_next = initial.vs_alloca_next /\
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

Theorem prefix_canonical_bulk_paired_allocations:
  ~(is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
  (^canonical_pair_allocations) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  disch_then (strip_assume_tac o SIMP_RULE bool_ss []) >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >> gnvs[Excl "enc_def"] >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var (Var dst) /\
   abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    (Cases_on `src` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= initial.vs_alloca_next /\
   initial.vs_alloca_next < dimword (:256)` by
    (drule_all alloca_frontier_inv_bound >> strip_tac >> decide_tac) >>
  `abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn))) (ListV avs) (ArrayV (DynArrayV vs))
    st st.cs_next_id src (Var dst) DLOAD (Lit 0w) (Lit 0w) 0 sb d initial.vs_alloca_next 0
    (abi_decoder_prune_vars st.cs_next_var initial)` by
    (irule ctor_actual_bulk_empty_window_pre >>
     asm_simp_tac bool_ss [vyper_to_abi_type_def] >>
     goal_assum (drule_at Any)) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def]) >>
  qpat_x_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def]) >>
  gnvs[Excl "enc_def"] >>
  drule_all abi_decoder_bulk_reentry_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') initial = OK t` >>
  drule_all prefix_copy_bulk_sim >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
  qabbrev_tac `actual = t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  rule_assum_tac (PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `abi_decode_sim ctx func initial
    (t with vs_inst_idx := LENGTH st'.cs_current_insts)` by metis_tac[] >>
  drule_all prefix_copy_transport >> strip_tac >>
  drule_all prefix_copy_canonical_dynarray_package >> strip_tac >>
  drule_all abi_decoder_bulk_pre_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_load DLOAD (n2w sb:bytes32) initial = n2w (LENGTH vs)` by
    (qpat_x_assum `abi_decode_load _ _ _ = _` mp_tac >>
     simp[abi_decode_load_def, abi_decode_source_def, abi_decoder_prune_vars_def]) >>
  `d < dimword (:256)` by decide_tac >>
  `32+LENGTH vs * type_memory_size tv <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    metis_tac[] >>
  `b <= w2n (n2w d:bytes32) /\
   w2n (n2w d:bytes32)+32+LENGTH vs * type_memory_bytes ce ty <= b+sz /\
   w2n (n2w d:bytes32)+32+LENGTH vs * type_memory_bytes ce ty < dimword (:256)` by
    (simp[] >> decide_tac) >>
  drule_all prefix_bulk_success_ghost >>
  disch_then (qspecl_then [`PG`,`Ddead`] strip_assume_tac) >>
  `actual.vs_allocas = initial.vs_allocas /\
   actual.vs_alloca_next = initial.vs_alloca_next` by simp[] >>
  qexistsl [`actual`,`H`,`qt`,`range_bytes [(d,32+LENGTH vs * type_memory_size tv)]`] >>
  asm_rewrite_tac[] >>
  conj_tac >- (qpat_x_assum `DISJOINT _ _` mp_tac >> simp[]) >>
  simp[op_taint_def] >> metis_tac[]
QED

Theorem prefix_canonical_bulk_paired:
  ~(is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
  (^canonical_pair) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule prefix_canonical_bulk_paired_allocations >> BETA_TAC >>
  disch_then (drule_all_then (qspecl_then [`Ddead`,`PG`] strip_assume_tac)) >>
  qexistsl [`actual`,`H`,`qt`,`B`] >> asm_rewrite_tac[]
QED

val _ = export_theory();
