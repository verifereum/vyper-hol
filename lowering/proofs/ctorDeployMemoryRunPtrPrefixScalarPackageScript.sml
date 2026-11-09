(* Clamp-independent scalar endpoint packaging. *)
Theory ctorDeployMemoryRunPtrPrefixScalarPackage
Ancestors
  loweringStateRelDefs valueEncodingDefs
  ctorDeployMemoryRunPtrPrefixCanonical ctorAbiActualWordRun
  ctorAbiActualWorld ctorAbiActualObservations abiDecoderReentryPointer
  abiDecoderReentry abiDecoderClampedWord
  abiDecoderWordTyped abiDecoderTypedContract abiDecoderLayout
  abiDecoderCoherence abiDecoderContract abiDecoderLoop
  abiEncoderRegisteredEffect allocaBudgetProps venomMemDefs
  abiEncoder valueEncoding valueEncodingProps valueEncodingProofs vyperTyping
  fragExec instIdxIndep allocaFrontierBound ctorAbiActualFrame
  venomState venomInst venomExecSemantics compileEnv exprLoweringProps
  memLocDefs ptrDiscipline words list pred_set finite_map

Theorem prefix_scalar_support:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  val_in_memory tv v d m /\
  (!a. a IN range_bytes [(d,32)] ==>
       mem_bytes_at a 1 mem = mem_bytes_at a 1 m) ==>
  type_memory_bytes ce ty = 32 /\ val_in_memory tv v d mem
Proof
  strip_tac >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  `mem_word_at d mem = mem_word_at d m` by
    (simp[mem_word_at_def, GSYM mem_bytes_at_def] >> AP_TERM_TAC >>
     irule prefix_canonical_support_window >> qexists `range_bytes [(d,32)]` >>
     simp[range_bytes_def]) >>
  `value_has_type tv v` by gvs[abi_decoder_metadata_def] >>
  Cases_on `v` >> gvs[value_has_type_def, val_in_memory_def] >>
  Cases_on `bt` >> gvs[is_word_type_def, value_has_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[is_word_type_def, value_has_type_def, val_in_memory_def]
QED

Theorem prefix_scalar_sim:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) (Lit 0w)
    (DecPrimWord clamp) st = ((),st') /\
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
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `frag_exec ctx st st' (\s. s = initial)
     (\s. s = t with vs_inst_idx := LENGTH st'.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[] >> gvs[EVERY_CONJ]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[]
QED

Theorem prefix_scalar_prepare:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),st') /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
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
  type_memory_bytes ce ty = 32 /\
  ?t. run_inst_seq (emitted_insts st st') initial = OK t /\
    val_in_memory tv v d t.vs_memory /\ fresh_vars_wrt limit_st t /\
    abi_decode_frame d 32 initial t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = 32` by
    (qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
      (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
     drule_all abi_decoder_descended_encoding_length >> simp[]) >>
  `sb < dimword (:256) /\ d < dimword (:256)` by
    (drule_all alloca_frontier_inv_bound >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var (Var dst)` by
    (Cases_on `src` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
     (DecPrimWord clamp) st = ((),st') /\
   mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av` by
    metis_tac[] >>
  drule_all ctor_actual_word_ceiling_sequence >>
  strip_tac >> asm_rewrite_tac[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem prefix_scalar_transport:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
    (DecPrimWord clamp) st = ((),st') /\
  run_inst_seq (emitted_insts st st') initial = OK t /\
  val_in_memory tv v d t.vs_memory /\ fresh_vars_wrt limit_st t /\
  abi_decode_frame d 32 initial t /\
  (!op w. abi_decoder_operand_live st.cs_next_var op /\
    eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
  t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
  fn_has_code st st' func /\ alloca_inv initial /\
  alloca_frontier_inv ctx func site initial /\
  ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  actual = (t with vs_inst_idx := LENGTH st'.cs_current_insts) ==>
  val_in_memory tv v d actual.vs_memory /\
  abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
    [(d,32)] initial actual /\
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
  drule_all prefix_scalar_sim >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
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
  conj_tac >- ( `alloca_inv t` by metis_tac[] >>
    pop_assum mp_tac >>
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

Theorem prefix_scalar_support_package:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  val_in_memory tv v d actual.vs_memory ==>
  FINITE (range_bytes [(d,32)]) /\
  range_bytes [(d,32)] SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\
  (!mem. (!a. a IN range_bytes [(d,32)] ==>
    mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
    val_in_memory tv v d mem)
Proof
  strip_tac >>
  `type_memory_bytes ce ty = 32` by
    (drule abi_decoder_primitive_cases >>
     disch_then (qspec_then `clamp` mp_tac) >> simp[]) >>
  asm_rewrite_tac[SUBSET_REFL] >>
  conj_tac
  >- (irule SUBSET_FINITE_I >> qexists `count (d+32)` >>
      simp[range_bytes_def, SUBSET_DEF]) >>
  rpt strip_tac >> drule_all prefix_scalar_support >> simp[]
QED

val _ = export_theory();
