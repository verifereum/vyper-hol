(* Shifted allocation credit and complete observations for coherent decoders. *)
Theory ctorDeployLoweringEntryDecoder
Ancestors
  loweringStateRelDefs
 ctorDeployLoweringEntryNoAlloc ctorDeployLoweringEntryArrayFrame
 ctorDeployLoweringEntryMember ctorDeployLoweringEntryArrayRun
 ctorDeployLoweringEntryRegistration ctorDeployMemoryFrontier
 ctorAbiActualNarrowWord abiDecoderCoherence abiDecoderContract
 abiDecoderWordTyped abiDecoderLayout abiDecoderTypedContract
 ctorAbiActualBulk abiDecoderCorrectPrimitiveArray abiDecoderBulkReentry
 vyperABI vyperTypeABI exprLowering
 abiDecoderReentry abiDecoderReentryPointer abiDecoderLoop
 abiDecoderVarSequence abiEncoderRegisteredEffect fragExec compileEnv
 valueEncoding venomState venomInst words list arithmetic

val Ck = ``\ty tv.
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
 actual.vs_labels = initial.vs_labels /\ actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code``;

Theorem deploy_ctor_primitive_run:
 type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==> (^Ck) ty tv
Proof
 strip_tac >> BETA_TAC >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
 asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `LENGTH (enc (vyper_to_abi_type env ty) av) = 32` by
   (qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
     (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
    drule_all abi_decoder_descended_encoding_length >> simp[]) >>
 `sb < dimword (:256) /\ d < dimword (:256)` by
   (drule_all deploy_ctor_shifted_frontier_bound >> strip_tac >> decide_tac) >>
 `abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst` by
   (Cases_on `src` >> Cases_on `dst` >>
    simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
    metis_tac[not_fresh_at_def]) >>
 `compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') /\
  mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av` by metis_tac[] >>
 qpat_assum `type_memory_bytes ce ty = 32` (fn th =>
   irule (PURE_REWRITE_RULE [th] deploy_ctor_noalloc_shifted_run)) >>
 asm_rewrite_tac[] >>
 drule_all deploy_ctor_scalar_frame_fragment >>
 simp[frag_exec_def] >> rpt strip_tac >>
 first_x_assum drule_all >> simp[] >>
 disch_then (qspecl_then [`site`, `func`, `ctx`] strip_assume_tac) >>
 qexists `t` >> asm_rewrite_tac[]
QED

Theorem deploy_ctor_bytes_run:
 type_to_abi_dec_info sf ce ty = DecBytestring n ==> (^Ck) ty tv
Proof
 strip_tac >> BETA_TAC >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `sb < dimword (:256) /\ d < dimword (:256) /\
  type_memory_bytes ce ty < dimword (:256)` by
   (drule_all deploy_ctor_shifted_frontier_bound >> strip_tac >> decide_tac) >>
 `abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi` by
   (Cases_on `src` >> Cases_on `dst` >> Cases_on `hi` >>
    simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
    metis_tac[not_fresh_at_def]) >>
 `compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecBytestring n) st = ((),st')` by metis_tac[] >>
 irule deploy_ctor_noalloc_shifted_run >> asm_rewrite_tac[] >>
 drule_all deploy_ctor_bytestring_frame_fragment >>
 simp[frag_exec_def] >> rpt strip_tac >>
 first_x_assum drule_all >> simp[] >>
 disch_then (qspecl_then [`site`, `func`, `ctx`] strip_assume_tac) >>
 qexists `t` >> asm_rewrite_tac[]
QED

Theorem deploy_ctor_dynamic_array_bulk_run:
 ~(is_abi_dynamic ce.ce_struct_fields ty \/
   dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
 (^Ck) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
 disch_then (strip_assume_tac o SIMP_RULE bool_ss []) >>
 simp_tac bool_ss [] >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule abi_decoder_dynarray_metadata_shape >> strip_tac >> gnvs[Excl "enc_def"] >>
 `abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
   (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
   (ListV avs) (ArrayV (DynArrayV vs))` by fs[abi_decoder_metadata_def] >>
 `abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi` by
   (qpat_x_assum `!x. src = Var x \/ _ ==> not_fresh_at st x` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    Cases_on `src` >> Cases_on `dst` >> Cases_on `hi` >>
    simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
    metis_tac[]) >>
 `d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= initial.vs_alloca_next /\
  initial.vs_alloca_next < dimword (:256)` by
   (drule_all deploy_ctor_shifted_frontier_bound >> strip_tac >> decide_tac) >>
 `abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
   (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn))) (ListV avs) (ArrayV (DynArrayV vs))
   st st.cs_next_id src dst DLOAD (Lit 0w) hi 0 sb d initial.vs_alloca_next 0
   (abi_decoder_prune_vars st.cs_next_var initial)` by
   (irule ctor_actual_bulk_empty_window_pre >>
    asm_simp_tac bool_ss [vyper_to_abi_type_def] >> goal_assum (drule_at Any)) >>
 qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
   (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def]) >>
 qpat_x_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
   (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def]) >>
 gnvs[Excl "enc_def"] >>
 irule deploy_ctor_noalloc_shifted_run >> asm_rewrite_tac[] >>
 drule_all deploy_ctor_bulk_frame_fragment >>
 simp[frag_exec_def] >> rpt strip_tac >>
 first_x_assum drule_all >> simp[] >>
 disch_then (qspecl_then [`site`, `func`, `ctx`] strip_assume_tac) >>
 qexists `actual` >> asm_rewrite_tac[]
QED

Theorem deploy_ctor_base_run:
 (^Ck) (BaseT bt) (BaseTV bt)
Proof
 `(?clamp. type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord clamp) \/
  (?n. type_to_abi_dec_info sf ce (BaseT bt) = DecBytestring n)` by
   (Cases_on `bt` >> simp[type_to_abi_dec_info_def] >>
    rename1 `BytesT bound` >> Cases_on `bound` >> simp[type_to_abi_dec_info_def])
 >- (irule deploy_ctor_primitive_run >> goal_assum (drule_at Any)) >>
 irule deploy_ctor_bytes_run >> goal_assum (drule_at Any)
QED

Theorem deploy_ctor_flag_run:
 (^Ck) (FlagT nsid) (FlagTV n)
Proof
 irule deploy_ctor_primitive_run >> simp[Once type_to_abi_dec_info_def]
QED

Theorem deploy_ctor_dynamic_array_run:
 (^Ck) ty tv ==> (^Ck) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
 strip_tac >>
 Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
   dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
 >- (match_mp_tac deploy_ctor_dynamic_array_loop_run >> asm_rewrite_tac[]) >>
 match_mp_tac deploy_ctor_dynamic_array_bulk_run >> asm_rewrite_tac[]
QED

Theorem deploy_ctor_array_run:
 (^Ck) ty tv ==> (^Ck) (ArrayT ty bd) (ArrayTV tv bd)
Proof
 Cases_on `bd`
 >- MATCH_ACCEPT_TAC deploy_ctor_fixed_array_run >>
 MATCH_ACCEPT_TAC deploy_ctor_dynamic_array_run
QED

Theorem deploy_ctor_coherent_run:
 !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> (^Ck) ty tv
Proof
 qabbrev_tac `P = \ce env sf. (^Ck)` >>
 `!ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> P ce env sf ty tv` suffices_by
   simp[Abbr `P`] >>
 ho_match_mp_tac abi_decoder_coherent_ind >>
 conj_tac
 >- (rpt gen_tac >> disch_tac >> simp_tac bool_ss [Abbr `P`] >>
     MATCH_ACCEPT_TAC (BETA_RULE deploy_ctor_base_run)) >>
 conj_tac
 >- (rpt gen_tac >> disch_tac >> simp_tac bool_ss [Abbr `P`] >>
     MATCH_ACCEPT_TAC (BETA_RULE deploy_ctor_flag_run)) >>
 conj_tac
 >- (rpt gen_tac >> strip_tac >> FULL_SIMP_TAC bool_ss [Abbr `P`] >>
     match_mp_tac (BETA_RULE deploy_ctor_array_run) >> first_assum ACCEPT_TAC) >>
 conj_tac
 >- (rpt gen_tac >> strip_tac >> FULL_SIMP_TAC bool_ss [Abbr `P`] >>
     match_mp_tac (BETA_RULE deploy_ctor_tuple) >> first_assum ACCEPT_TAC) >>
 rpt gen_tac >> strip_tac >> FULL_SIMP_TAC bool_ss [Abbr `P`] >>
 match_mp_tac (BETA_RULE deploy_ctor_struct) >> asm_rewrite_tac[]
QED
