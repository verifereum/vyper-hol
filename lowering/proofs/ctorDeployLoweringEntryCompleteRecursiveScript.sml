Theory ctorDeployLoweringEntryCompleteRecursive
Ancestors
  ctorDeployLoweringEntryCompleteMember ctorDeployLoweringEntryCompleteArray
  ctorDeployLoweringEntryCompleteScalar ctorDeployLoweringEntryCompleteNoAlloc
  abiDecoderTupleInputs abiDecoderTypedContract valueEncodingProps
  abiDecoderStruct abiStaticDynarrayLayout valueEncodingTyping vyperTyping
  abiDecoderFixedInputs abiCanonicalHeadSize abiDecoderFixedMemory
  abiDecoderMemberInfos abiDecoderMembers abiDecoderCoherence
  abiDecoderContract abiEncoderProps abiEncoder compileEnv exprLoweringProps exprLowering
  vyperTypeABI vyperABI valueEncoding contractABI rich_list finite_map
  fragGasPath venomExecSemantics venomState venomInst words list arithmetic

val Ccomplete = ``\ty tv.
 !dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
 compile_abi_decode_to_buf dst src DLOAD hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
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

Theorem deploy_ctor_tuple_complete:
  LIST_REL (^Ccomplete) tys tvs ==> (^Ccomplete) (TupleT tys) (TupleTV tvs)
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_to_vyper env (TupleT tys) av = SOME v` by
    fs[abi_decoder_metadata_def] >>
  drule abi_decoder_tuple_values >> strip_tac >>
  qpat_x_assum `av = ListV _` SUBST_ALL_TAC >>
  qpat_x_assum `v = ArrayV _` SUBST_ALL_TAC >>
  drule_all abi_decoder_tuple_members >> strip_tac >>
  `type_memory_bytes ce (TupleT tys) = SUM (MAP (type_memory_bytes ce) tys)` by
    (simp[Once type_memory_bytes_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_tuple_infos]) >>
  `vyper_to_abi_type env (TupleT tys) = Tuple (MAP (vyper_to_abi_type env) tys)` by
    simp[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP] >>
  mp_tac (Q.INST [`final` |-> `st'`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields) tys`] deploy_ctor_complex_execute_complete) >>
  (impl_tac >- (NO_STRIP_FULL_SIMP_TAC bool_ss [vyper_to_abi_types_MAP] >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >> qexists `actual` >> asm_simp_tac bool_ss [val_in_memory_tuple]
QED

val Ccompletedesc = ``(\env sf. ^Ccomplete) (env \\ nsid) (sf \\ nsid_to_string nsid)``;

Theorem deploy_ctor_struct_complete:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  LIST_REL (^Ccompletedesc) (MAP SND args) tvs ==>
  (^Ccomplete) (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH tvs = LENGTH args` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_to_vyper env (StructT nsid) av = SOME v` by fs[abi_decoder_metadata_def] >>
  drule abi_decoder_struct_values >> strip_tac >>
  qpat_x_assum `av = ListV _` SUBST_ALL_TAC >>
  qpat_x_assum `v = StructV _` SUBST_ALL_TAC >>
  drule_all abi_decoder_struct_members_at >> strip_tac >>
  drule abi_decoder_members_relations >> strip_tac >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (irule type_memory_size_fields_zip >> simp[]) >>
  `type_memory_bytes ce (StructT nsid) = SUM (MAP (type_memory_bytes ce) (MAP SND args))` by
    fs[abi_decoder_metadata_def, Once type_memory_size_def, Excl "enc_def"] >>
  drule_all abi_decoder_struct_field_types >> strip_tac >>
  drule abi_decoder_struct_infos >> strip_tac >>
  `vyper_to_abi_type env (StructT nsid) =
    Tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))` by
    simp[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP] >>
  mp_tac (Q.INST [`final` |-> `st'`,
    `env` |-> `env \\ nsid`, `sf` |-> `sf \\ nsid_to_string nsid`,
    `tys` |-> `MAP SND (args:(string # vyperAST$type) list)`,
    `vs` |-> `MAP SND (fields:(string # value) list)`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields)
      (MAP SND (args:(string # vyperAST$type) list))`] deploy_ctor_complex_execute_complete) >>
  (impl_tac >- (NO_STRIP_FULL_SIMP_TAC bool_ss [vyper_to_abi_types_MAP] >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `fields_in_memory fields (ZIP (MAP FST args,tvs)) d actual.vs_memory` by
    (irule static_fields_memory_zip >> fs[abi_decoder_metadata_def, Once value_has_type_def]) >>
  qexists `actual` >> asm_simp_tac bool_ss [val_in_memory_struct]
QED

Theorem deploy_ctor_fixed_array_run_complete:
 (^Ccomplete) ty tv ==> (^Ccomplete) (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
Proof
 strip_tac >> simp_tac bool_ss [] >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule_all abi_decoder_fixed_array_values >> strip_tac >>
 gnvs[Once vyper_to_abi_type_def, canonical_array_tuple, Excl "enc_def"] >>
 qpat_assum `LENGTH vs = LENGTH avs`
   (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th]) >> assume_tac th) >>
 `type_memory_bytes ce (ArrayT ty (Fixed (LENGTH vs))) =
   LENGTH vs * type_memory_bytes ce ty` by simp[Once type_memory_bytes_def] >>
 qpat_assum `type_memory_bytes ce (ArrayT ty (Fixed (LENGTH vs))) = _`
   (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
 `LIST_REL (^Ccomplete) (REPLICATE (LENGTH vs) ty) (REPLICATE (LENGTH vs) tv)` by
   (simp_tac bool_ss [LIST_REL_REPLICATE_same] >> BETA_TAC >>
    strip_tac >> first_assum ACCEPT_TAC) >>
 qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
   (assume_tac o PURE_REWRITE_RULE [abi_decoder_fixed_array_infos]) >>
 drule_all (SIMP_RULE bool_ss [map_replicate, SUM_REPLICATE]
   (Q.INST [`tys` |-> `REPLICATE (LENGTH vs) ty`,
     `tvs` |-> `REPLICATE (LENGTH vs) tv`] (BETA_RULE deploy_ctor_complex_execute_complete))) >>
 disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 qexists `actual` >>
 qpat_x_assum `LENGTH vs = LENGTH avs` (fn th => rewrite_tac[GSYM th]) >>
 asm_simp_tac bool_ss [Once type_memory_bytes_def] >>
 irule abi_decoder_fixed_array_memory >> asm_simp_tac bool_ss []
QED

Theorem deploy_ctor_base_run_complete:
 (^Ccomplete) (BaseT bt) (BaseTV bt)
Proof
 `(?clamp. type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord clamp) \/
  (?n. type_to_abi_dec_info sf ce (BaseT bt) = DecBytestring n)` by
   (Cases_on `bt` >> simp[type_to_abi_dec_info_def] >>
    rename1 `BytesT bound` >> Cases_on `bound` >> simp[type_to_abi_dec_info_def])
 >- (irule deploy_ctor_primitive_run_complete >> goal_assum (drule_at Any)) >>
 irule deploy_ctor_bytes_run_complete >> goal_assum (drule_at Any)
QED

Theorem deploy_ctor_flag_run_complete:
 (^Ccomplete) (FlagT nsid) (FlagTV n)
Proof
 irule deploy_ctor_primitive_run_complete >> simp[Once type_to_abi_dec_info_def]
QED

Theorem deploy_ctor_array_run_complete:
 (^Ccomplete) ty tv ==> (^Ccomplete) (ArrayT ty bd) (ArrayTV tv bd)
Proof
 Cases_on `bd`
 >- MATCH_ACCEPT_TAC deploy_ctor_fixed_array_run_complete >>
 MATCH_ACCEPT_TAC deploy_ctor_dynamic_array_run_complete
QED

Theorem deploy_ctor_coherent_run_complete:
 !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> (^Ccomplete) ty tv
Proof
 qabbrev_tac `P = \ce env sf. (^Ccomplete)` >>
 `!ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> P ce env sf ty tv` suffices_by
   simp[Abbr `P`] >>
 ho_match_mp_tac abi_decoder_coherent_ind >>
 conj_tac
 >- (rpt gen_tac >> disch_tac >> simp_tac bool_ss [Abbr `P`] >>
     MATCH_ACCEPT_TAC (BETA_RULE deploy_ctor_base_run_complete)) >>
 conj_tac
 >- (rpt gen_tac >> disch_tac >> simp_tac bool_ss [Abbr `P`] >>
     MATCH_ACCEPT_TAC (BETA_RULE deploy_ctor_flag_run_complete)) >>
 conj_tac
 >- (rpt gen_tac >> strip_tac >> FULL_SIMP_TAC bool_ss [Abbr `P`] >>
     match_mp_tac (BETA_RULE deploy_ctor_array_run_complete) >> first_assum ACCEPT_TAC) >>
 conj_tac
 >- (rpt gen_tac >> strip_tac >> FULL_SIMP_TAC bool_ss [Abbr `P`] >>
     match_mp_tac (BETA_RULE deploy_ctor_tuple_complete) >> first_assum ACCEPT_TAC) >>
 rpt gen_tac >> strip_tac >> FULL_SIMP_TAC bool_ss [Abbr `P`] >>
 match_mp_tac (BETA_RULE deploy_ctor_struct_complete) >> asm_rewrite_tac[]
QED

val CcompleteGas = ``\ty tv.
 !dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
 compile_abi_decode_to_buf dst src DLOAD hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\ abi_decoder_metadata ce env ty tv root_di av v /\
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
 ?actual. gas_path ctx func initial 0 (OK actual) /\ val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st')) [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx``;

Theorem deploy_ctor_tuple_complete_gas_path:
  LIST_REL (^CcompleteGas) tys tvs ==> (^CcompleteGas) (TupleT tys) (TupleTV tvs)
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_to_vyper env (TupleT tys) av = SOME v` by
    fs[abi_decoder_metadata_def] >>
  drule abi_decoder_tuple_values >> strip_tac >>
  qpat_x_assum `av = ListV _` SUBST_ALL_TAC >>
  qpat_x_assum `v = ArrayV _` SUBST_ALL_TAC >>
  drule_all abi_decoder_tuple_members >> strip_tac >>
  `type_memory_bytes ce (TupleT tys) = SUM (MAP (type_memory_bytes ce) tys)` by
    (simp[Once type_memory_bytes_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_tuple_infos]) >>
  `vyper_to_abi_type env (TupleT tys) = Tuple (MAP (vyper_to_abi_type env) tys)` by
    simp[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP] >>
  mp_tac (Q.INST [`final` |-> `st'`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields) tys`] deploy_ctor_complex_execute_complete_gas) >>
  (impl_tac >- (NO_STRIP_FULL_SIMP_TAC bool_ss [vyper_to_abi_types_MAP] >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >> qexists `actual` >> asm_simp_tac bool_ss [val_in_memory_tuple]
QED

val CcompletedescGas = ``(\env sf. ^CcompleteGas) (env \\ nsid) (sf \\ nsid_to_string nsid)``;

Theorem deploy_ctor_struct_complete_gas_path:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  LIST_REL (^CcompletedescGas) (MAP SND args) tvs ==>
  (^CcompleteGas) (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH tvs = LENGTH args` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_to_vyper env (StructT nsid) av = SOME v` by fs[abi_decoder_metadata_def] >>
  drule abi_decoder_struct_values >> strip_tac >>
  qpat_x_assum `av = ListV _` SUBST_ALL_TAC >>
  qpat_x_assum `v = StructV _` SUBST_ALL_TAC >>
  drule_all abi_decoder_struct_members_at >> strip_tac >>
  drule abi_decoder_members_relations >> strip_tac >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (irule type_memory_size_fields_zip >> simp[]) >>
  `type_memory_bytes ce (StructT nsid) = SUM (MAP (type_memory_bytes ce) (MAP SND args))` by
    fs[abi_decoder_metadata_def, Once type_memory_size_def, Excl "enc_def"] >>
  drule_all abi_decoder_struct_field_types >> strip_tac >>
  drule abi_decoder_struct_infos >> strip_tac >>
  `vyper_to_abi_type env (StructT nsid) =
    Tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))` by
    simp[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP] >>
  mp_tac (Q.INST [`final` |-> `st'`,
    `env` |-> `env \\ nsid`, `sf` |-> `sf \\ nsid_to_string nsid`,
    `tys` |-> `MAP SND (args:(string # vyperAST$type) list)`,
    `vs` |-> `MAP SND (fields:(string # value) list)`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields)
      (MAP SND (args:(string # vyperAST$type) list))`] deploy_ctor_complex_execute_complete_gas) >>
  (impl_tac >- (NO_STRIP_FULL_SIMP_TAC bool_ss [vyper_to_abi_types_MAP] >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `fields_in_memory fields (ZIP (MAP FST args,tvs)) d actual.vs_memory` by
    (irule static_fields_memory_zip >> fs[abi_decoder_metadata_def, Once value_has_type_def]) >>
  qexists `actual` >> asm_simp_tac bool_ss [val_in_memory_struct]
QED

Theorem deploy_ctor_fixed_array_run_complete_gas_path:
 (^CcompleteGas) ty tv ==> (^CcompleteGas) (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
Proof
 strip_tac >> simp_tac bool_ss [] >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule_all abi_decoder_fixed_array_values >> strip_tac >>
 gnvs[Once vyper_to_abi_type_def, canonical_array_tuple, Excl "enc_def"] >>
 qpat_assum `LENGTH vs = LENGTH avs`
   (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th]) >> assume_tac th) >>
 `type_memory_bytes ce (ArrayT ty (Fixed (LENGTH vs))) =
   LENGTH vs * type_memory_bytes ce ty` by simp[Once type_memory_bytes_def] >>
 qpat_assum `type_memory_bytes ce (ArrayT ty (Fixed (LENGTH vs))) = _`
   (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
 `LIST_REL (^CcompleteGas) (REPLICATE (LENGTH vs) ty) (REPLICATE (LENGTH vs) tv)` by
   (simp_tac bool_ss [LIST_REL_REPLICATE_same] >> BETA_TAC >>
    strip_tac >> first_assum ACCEPT_TAC) >>
 qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
   (assume_tac o PURE_REWRITE_RULE [abi_decoder_fixed_array_infos]) >>
 drule_all (SIMP_RULE bool_ss [map_replicate, SUM_REPLICATE]
   (Q.INST [`tys` |-> `REPLICATE (LENGTH vs) ty`,
     `tvs` |-> `REPLICATE (LENGTH vs) tv`] (BETA_RULE deploy_ctor_complex_execute_complete_gas))) >>
 disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 qexists `actual` >>
 qpat_x_assum `LENGTH vs = LENGTH avs` (fn th => rewrite_tac[GSYM th]) >>
 asm_simp_tac bool_ss [Once type_memory_bytes_def] >>
 irule abi_decoder_fixed_array_memory >> asm_simp_tac bool_ss []
QED

Theorem deploy_ctor_base_run_complete_gas_path:
 (^CcompleteGas) (BaseT bt) (BaseTV bt)
Proof
 `(?clamp. type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord clamp) \/
  (?n. type_to_abi_dec_info sf ce (BaseT bt) = DecBytestring n)` by
   (Cases_on `bt` >> simp[type_to_abi_dec_info_def] >>
    rename1 `BytesT bound` >> Cases_on `bound` >> simp[type_to_abi_dec_info_def])
 >- (irule deploy_ctor_primitive_run_complete_gas_path >> goal_assum (drule_at Any)) >>
 irule deploy_ctor_bytes_run_complete_gas_path >> goal_assum (drule_at Any)
QED

Theorem deploy_ctor_flag_run_complete_gas_path:
 (^CcompleteGas) (FlagT nsid) (FlagTV n)
Proof
 irule deploy_ctor_primitive_run_complete_gas_path >> simp[Once type_to_abi_dec_info_def]
QED

Theorem deploy_ctor_array_run_complete_gas_path:
 (^CcompleteGas) ty tv ==> (^CcompleteGas) (ArrayT ty bd) (ArrayTV tv bd)
Proof
 Cases_on `bd`
 >- MATCH_ACCEPT_TAC deploy_ctor_fixed_array_run_complete_gas_path >>
 MATCH_ACCEPT_TAC deploy_ctor_dynamic_array_run_complete_gas_path
QED

Theorem deploy_ctor_coherent_run_complete_gas_path:
 !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> (^CcompleteGas) ty tv
Proof
 qabbrev_tac `P = \ce env sf. (^CcompleteGas)` >>
 `!ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> P ce env sf ty tv` suffices_by
   simp[Abbr `P`] >>
 ho_match_mp_tac abi_decoder_coherent_ind >>
 conj_tac
 >- (rpt gen_tac >> disch_tac >> simp_tac bool_ss [Abbr `P`] >>
     MATCH_ACCEPT_TAC (BETA_RULE deploy_ctor_base_run_complete_gas_path)) >>
 conj_tac
 >- (rpt gen_tac >> disch_tac >> simp_tac bool_ss [Abbr `P`] >>
     MATCH_ACCEPT_TAC (BETA_RULE deploy_ctor_flag_run_complete_gas_path)) >>
 conj_tac
 >- (rpt gen_tac >> strip_tac >> FULL_SIMP_TAC bool_ss [Abbr `P`] >>
     match_mp_tac (BETA_RULE deploy_ctor_array_run_complete_gas_path) >> first_assum ACCEPT_TAC) >>
 conj_tac
 >- (rpt gen_tac >> strip_tac >> FULL_SIMP_TAC bool_ss [Abbr `P`] >>
     match_mp_tac (BETA_RULE deploy_ctor_tuple_complete_gas_path) >> first_assum ACCEPT_TAC) >>
 rpt gen_tac >> strip_tac >> FULL_SIMP_TAC bool_ss [Abbr `P`] >>
 match_mp_tac (BETA_RULE deploy_ctor_struct_complete_gas_path) >> asm_rewrite_tac[]
QED

