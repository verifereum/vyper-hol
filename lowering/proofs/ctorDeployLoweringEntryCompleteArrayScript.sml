(* Dynamic-array integration of complete preparation and finite iteration. *)
Theory ctorDeployLoweringEntryCompleteArray
Ancestors
  loweringStateRelDefs
  ctorDeployLoweringEntryCompleteArrayRun ctorDeployLoweringEntryCompletePrefix
  ctorDeployLoweringEntryCompleteNoAlloc ctorDeployLoweringEntryArrayRun
  ctorDeployLoweringEntryArrayOps ctorDeployLoweringEntryRegistration
  ctorAbiActualArrayBody ctorAbiActualArrayIteration ctorAbiActualArrayInvariant
  ctorAbiActualFrame ctorAbiActualWorld ctorAbiActualNarrow
  abiDecoderDynamicLoopSetup abiDecoderArraySetupInputs abiDecoderContract
  abiDecoderReentry abiDecoderVarSequence abiDecoderArraySetupCode
  abiDecoderLoop fragExec instIdxIndep compileEnv venomExecSemantics venomState
  ctorDeployLoweringEntryArrayFrame ctorDeployMemoryFrontier ctorAbiActualChildFrame
  ctorAbiActualMemory ctorAbiActualSites abiDecoderArrayPrefix valueEncodingTyping
  abiDecoderArrayInvariant abiEncoderRegisteredEffect valueEncoding words list rich_list arithmetic
  finite_map pred_set venomMemDefs venomMemProofs vyperTyping abiDecoderLoopRegisters
  abiDecoderExecution abiDecoderArrayBackedge abiDecoderReentryAddress
  valueEncodingProps abiEncoderPrimitiveEffect abiEncoderProps abiDecoderCode
  abiDecoderIndexedAddress entryDecodeStructure emitHelper abiDecoderLoopSetup
  ctorAbiActualObservations abiDecoderRecursiveLoopContext abiCanonicalHeadSize
  ctorAbiActualArrayFinite abiDecoderTypedContract ctorAbiActualArrayRun
  ctorAbiActualArrayLayout ctorAbiActualArrayContext ctorAbiActualArrayEntry
  abiDecoderCorrectPrimitiveArray exprLowering ctorDeployLoweringEntryAllocation
  abiDecoderIndexInit ASCIInumbers abiDecoderArrayLoopInit abiDecoderRecursiveLoopEntry
  abiDecoderRecursiveLoopLayout

val Ccomplete = ``\ty tv.
 !dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
 compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\ sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
 (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\ k + unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st')) [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx``;

val Ok = ``\k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot base prefix cursor s.
    prefix <= LENGTH vs /\ cursor <= LENGTH vs /\
    elems_in_memory (TAKE prefix vs) (d+32) tv s.vs_memory /\
    mload d s = n2w (LENGTH vs) /\
    FLOOKUP s.vs_allocas slot_id = SOME (slot,32) /\ mload slot s = n2w cursor /\
    alloca_inv s /\ alloca_frontier_inv_from k ctx func site s /\
    ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next /\
    fresh_vars_wrt limit_st s /\ s.vs_data_section = base.vs_data_section /\
    s.vs_call_ctx = base.vs_call_ctx /\ s.vs_labels = base.vs_labels /\
    (!x w. abi_decoder_older_vars next x /\ lookup_var x base = SOME w ==>
      lookup_var x s = SOME w) /\
    abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] base s /\
    s.vs_gas_readings = base.vs_gas_readings /\ s.vs_code = base.vs_code``;

(* The original scratch enlargement theorem is local to ArrayRun. *)
Theorem deploy_ctor_complete_array_scratch_enlarge[local]:
 small SUBSET ids /\ ctor_actual_scratch func small D N final /\
 abi_encoder_registered_effect (ctor_actual_sites func small) regions initial final /\
 ctor_actual_scratch func ids D N initial ==>
 ctor_actual_scratch func ids D N final
Proof
 strip_tac >> simp_tac bool_ss [ctor_actual_scratch_def] >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 Cases_on `inst.inst_id IN small`
 >- (qpat_x_assum `ctor_actual_scratch func small _ _ final` mp_tac >>
     simp_tac bool_ss [ctor_actual_scratch_def] >>
     disch_then (qspecl_then [`inst`, `b`, `sz`] mp_tac) >> asm_rewrite_tac[]) >>
 `inst.inst_id NOTIN ctor_actual_sites func small` by simp[ctor_actual_sites_def] >>
 qpat_x_assum `abi_encoder_registered_effect _ _ initial final` mp_tac >>
 simp_tac bool_ss [abi_encoder_registered_effect_def] >> strip_tac >>
 `FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz)` by metis_tac[] >>
 qpat_x_assum `ctor_actual_scratch func ids _ _ initial` mp_tac >>
 simp_tac bool_ss [ctor_actual_scratch_def] >>
 disch_then (qspecl_then [`inst`, `b`, `sz`] mp_tac) >> asm_rewrite_tac[]
QED

Theorem deploy_ctor_dynamic_array_loop_run_complete:
 (^Ccomplete) ty tv /\
 (is_abi_dynamic ce.ce_struct_fields ty \/
   dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
 (^Ccomplete) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
 qabbrev_tac `Child = (^Ccomplete) ty tv` >>
 disch_then (CONJUNCTS_THEN2 (mk_asm "child") assume_tac) >>
 simp_tac bool_ss [] >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule abi_decoder_dynarray_metadata_shape >> strip_tac >> gnvs[Excl "enc_def"] >>
 `abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
    (ListV avs) (ArrayV (DynArrayV vs))` by fs[abi_decoder_metadata_def] >>
 `compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi
    (DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
      (is_abi_dynamic ce.ce_struct_fields ty) maxn) st = ((),st')` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
     simp_tac bool_ss [Once type_to_abi_dec_info_def]) >>
 drule_all ctor_actual_array_loop_layout >> strip_tac >>
 drule_all ctor_actual_array_prefix_inputs >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi` by
   (Cases_on `src` >> Cases_on `dst` >> Cases_on `hi` >>
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
 `loop_st.cs_next_var <= limit_st.cs_next_var` by
   fs[abi_decoder_recursive_loop_compiled_def] >>
 `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\ d+32 <= D+N` by
   fs[Once type_memory_bytes_def] >>
 `d < dimword (:256)` by
   (drule_all deploy_ctor_shifted_frontier_bound >> strip_tac >> decide_tac) >>
 `ctor_actual_scratch func (frag_ids st st') D N initial` by
   (irule ctor_actual_scratch_restrict >> goal_assum (drule_at Any) >> simp[]) >>
 `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func))` by
   (irule ctor_actual_function_ids >> simp[]) >>
 drule_all deploy_ctor_array_prefix_header_index_complete_entry >>
 disch_then (qspec_then `tv`
   (qx_choose_then `prepared` (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS)))) >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 `st.cs_next_var <= loop_st.cs_next_var` by
   (drule_all abi_decode_dynarray_checked_prefix_shape >> strip_tac >>
    drule_all abi_decode_array_header_shape >> strip_tac >>
    drule abi_decode_index_init_shape >> strip_tac >> decide_tac) >>
 drule_all deploy_ctor_array_setup_context >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule_all abi_decoder_loop_phase_entry >> disch_tac >>
 drule_all abi_decoder_recursive_compiled_facts >> strip_tac >>
 `?bb. lookup_block prepared.vs_current_bb func.fn_blocks = SOME bb /\
   bb.bb_instructions = loop_st.cs_current_insts ++
     [mk_inst loop_st.cs_next_id JMP [Label (FST labels)] []]` by simp[] >>
 pop_assum strip_assume_tac >>
 asm_x "child" mp_tac >> simp_tac bool_ss [Abbr `Child`] >> disch_tac >>
 `(^Ccomplete) ty tv` by (BETA_TAC >> first_assum ACCEPT_TAC) >>
 drule_all deploy_ctor_array_prepared_complete_run >>
 disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 qpat_assum `(^Ok) k ctx func site (frag_ids st st') D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) st.cs_next_var limit_st
   tv vs header_st.cs_next_id slot initial (LENGTH vs) (LENGTH vs) actual`
   (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE) >>
 `ctor_actual_scratch func ids D N actual` by
   (irule deploy_ctor_complete_array_scratch_enlarge >> goal_assum (drule_at Any) >> simp[]) >>
 qexists `actual` >> asm_simp_tac bool_ss [] >>
 conj_tac
 >- (rpt strip_tac >> first_x_assum irule >>
     fs[abi_decoder_older_vars_def, not_fresh_at_def]) >>
 drule abi_decoder_array_setup_head >> strip_tac >>
 qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
 asm_rewrite_tac[] >> disch_then (mp_tac o MATCH_MP abi_decoder_loop_suffix_facts) >> simp[]
QED

Theorem deploy_ctor_dynamic_array_run_complete:
 (^Ccomplete) ty tv ==>
 (^Ccomplete) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
 disch_tac >>
 Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
   dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
 >- (irule deploy_ctor_dynamic_array_loop_run_complete >> simp[]) >>
 irule deploy_ctor_dynamic_array_bulk_run_complete >> fs[]
QED
