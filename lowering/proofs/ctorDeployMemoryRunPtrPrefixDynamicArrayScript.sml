(* Same-witness floor-aware dynamic-array decoder: semantic observations,
   finite clean support and pointer-safe continuation at the actual endpoint. *)
Theory ctorDeployMemoryRunPtrPrefixDynamicArray
Ancestors
  loweringStateRelDefs valueEncodingDefs
  ctorDeployMemoryRunPtrPrefixLoopClose ctorAbiActualArrayRun ctorAbiActualArrayInvariant
  ctorAbiActualArrayContext valueEncoding valueEncodingProps
  abiDecoderContract abiDecoderTypedContract abiDecoderCorrectPrimitiveArray
  abiDecoderRecursiveLoopContext abiDecoderCoherence abiDecoderLoopEmit
  compileEnv exprLowering ptrSafeRun ptrDiscipline venomState pred_set
  ctorAbiActualSites ctorAbiActualFrame abiEncoderRegisteredEffect abiDecoderReentry
  abiDecoderCounters abiDecoderArrayLoopInit abiDecoderArraySetupCode abiDecoderIndexInit
  abiDecoderRecursiveArray abiDecoderLoop abiDecoderArrayInvariant arithmetic

val canonical_pair_floor = ``\ty tv.
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
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\ lo <= initial.vs_alloca_next ==>
 ?actual H qt B.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\
 FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\ DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
   val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
   op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)``;

Theorem prefix_array_scratch_transport[local]:
  frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
  ctor_actual_scratch func (frag_ids st st') D N actual /\
  abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st')) outs initial actual ==>
  ctor_actual_scratch func ids D N actual
Proof
  strip_tac >> simp_tac bool_ss [ctor_actual_scratch_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `inst.inst_id IN frag_ids st st'`
  >- (qpat_x_assum `ctor_actual_scratch func (frag_ids st st') _ _ actual` mp_tac >>
      simp_tac bool_ss [ctor_actual_scratch_def] >>
      disch_then (qspecl_then [`inst`,`b`,`sz`] mp_tac) >> asm_rewrite_tac []) >>
  `inst.inst_id NOTIN ctor_actual_sites func (frag_ids st st')` by
    simp[ctor_actual_sites_def] >>
  qpat_x_assum `abi_encoder_registered_effect _ _ initial actual` mp_tac >>
  simp_tac bool_ss [abi_encoder_registered_effect_def] >> strip_tac >>
  `FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz)` by metis_tac [] >>
  qpat_x_assum `ctor_actual_scratch func ids _ _ initial` mp_tac >>
  simp_tac bool_ss [ctor_actual_scratch_def] >>
  disch_then (qspecl_then [`inst`,`b`,`sz`] mp_tac) >> asm_rewrite_tac []
QED

Theorem prefix_dynamic_array_loop_paired_floor:
  (^canonical_pair_floor) ty tv /\
  (is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
  (^canonical_pair_floor) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") assume_tac) >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `ctor_actual_scratch func (frag_ids st st') D N initial` by
    (irule ctor_actual_scratch_restrict >> goal_assum (drule_at Any) >> simp[]) >>
  asm "child" assume_tac >>
  drule prefix_dynamic_array_setup_finite_pair_complete >>
  disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ctor_actual_scratch _ _ _ _ _`)) >>
  disch_then (mp_tac o PURE_REWRITE_RULE [SUBSET_REFL]) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`Ddead`,`PG`] mp_tac) >>
  strip_tac >>
  qpat_x_assum `child :- _` kall_tac >>
  qpat_x_assum `(^canonical_pair_floor) ty tv` kall_tac >>
  PairCases_on `Y` >> gnvs[Excl "enc_def"] >>
  qpat_x_assum `_ /\ _` (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  `st.cs_next_var <= loop_st.cs_next_var` by
    (drule_all abi_decode_dynarray_checked_prefix_shape >> strip_tac >>
     drule_all abi_decode_array_header_shape >> strip_tac >>
     drule abi_decode_index_init_shape >> strip_tac >> decide_tac) >>
  drule_all ctor_actual_array_observation_compose >> strip_tac >>
  qpat_assum `ctor_actual_array_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _ initial _ _ Y0`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [ctor_actual_array_observation_def]) >>
  qexistsl [`Y0`,`Y1`,`Y2`,`Y3`] >>
  asm_simp_tac bool_ss [] >>
  conj_tac
  >- (simp[val_in_memory_def, mem_word_at_eq_mload]) >>
  conj_tac
  >- (irule prefix_array_scratch_transport >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      fs[abi_decoder_older_vars_def,not_fresh_at_def]) >>
  conj_tac
  >- (irule abi_decode_sim_trans >> qexists `prepared` >> simp[] >>
      irule abi_decode_sim_trans >> qexists `jump_to (FST labels) prepared` >> simp[]) >>
  `LENGTH vs <= maxn` by
    (drule abi_decoder_dynarray_values >> simp[]) >>
  `type_memory_bytes ce (ArrayT ty (Dynamic maxn)) =
     32 + maxn * type_memory_size tv` by
    (drule abi_decoder_coherent_header >>
     simp[abi_decoder_header_def, type_memory_size_def]) >>
  conj_tac
  >- (irule SUBSET_TRANS >>
      qexists `range_bytes [(d,LENGTH vs * type_memory_size tv + 32)]` >>
      simp[] >> simp[SUBSET_DEF, range_bytes_def] >>
      rpt strip_tac >>
      `LENGTH vs * type_memory_size tv <= maxn * type_memory_size tv` by
        simp[] >>
      irule LESS_LESS_EQ_TRANS >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_assum `!mem. _ ==> mem_bytes_at d 32 mem = _ /\ _`
        (qspec_then `Y0.vs_memory` mp_tac) >> simp_tac bool_ss [] >> strip_tac >>
      qpat_x_assum `!mem. _ ==> mem_bytes_at d 32 mem = _ /\ _` drule >>
      strip_tac >> simp[val_in_memory_def] >>
      `mem_word_at d mem = mem_word_at d Y0.vs_memory` by
        metis_tac[mem_word_at_def,mem_bytes_at_def] >>
      simp[mem_word_at_eq_mload]) >>
  conj_tac >- metis_tac[SUBSET_TRANS] >>
  rpt strip_tac >>
  `abi_decoder_older_vars st.cs_next_var x /\
   abi_decoder_older_vars loop_st.cs_next_var x` by
    fs[abi_decoder_older_vars_def,not_fresh_at_def] >>
  metis_tac[]
QED


val _ = export_theory();
