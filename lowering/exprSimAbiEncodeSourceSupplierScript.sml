Theory exprSimAbiEncodeSourceSupplier
Ancestors
  exprSimAbiEncodeSourceTranslation exprSimAbiEncodeRegionInput
  abiEncoderSourceFootprint abiEncoderSourceProducer abiEncoderSourceWindow
  exprSimDefs exprSimProps loweringPosts valueEncoding vyperValue vyperTyping vyperABI
  abiEncoderProps abiEncoderOpenInput abiBuiltinAllocation contractABI compileEnv
  retAbiPlanProps exprSimAbiEncodePlanTranslation vyperTypeSystem finite_map list
  abiEncoderSourceAggregate abiTupleEncodeLayout valueEncodingTyping words abiEncodeInputSupplier
  exprSimAbiEncodePlanMetadata abiEncodeZeroSupplier abiTupleEncodeZeroInput
  abiEncoderSourcePrimitive abiCallerTupleLayout abiDecodeRanges abiEncodeTupleCongruence

Theorem abi_encode_translated_source_footprint:
  evaluate_type E ty = SOME tv /\ E SUBMAP E0 /\
  sfields_tenv_consistent sf E /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  value_has_type tv v /\ vyper_to_abi E ty v = SOME av /\
  val_in_memory tv v sb mem ==>
  ?ct rv. source_rep E ty (type_to_abi_enc_info sf ce ty) ct /\
    enc ct rv = enc (vyper_to_abi_type E ty) av /\
    abi_encoder_open_input (type_to_abi_enc_info sf ce ty) ct rv sb (val_footprint tv v) mem
Proof
  strip_tac >> Cases_on `val_footprint tv v = type_memory_size tv`
  >- (drule_all abi_encode_translated_source_window >> metis_tac[]) >>
  Cases_on `v` >> gvs[val_footprint_def] >>
  Cases_on `tv` >> gvs[] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> gvs[] >>
  Cases_on `ty` >> gvs[evaluate_type_def, AllCaseEqs()] >>
  qmatch_goalsub_abbrev_tac `source_rep E bty` >>
  `abi_enc_plan E bty (type_to_abi_enc_info sf ce bty)` by
    (irule abi_encode_translated_plan >> simp[Abbr `bty`, assignable_type_def, evaluate_type_def, well_formed_type_def] >>
     qexists `E0` >> simp[]) >>
  drule abi_encoder_source_footprint_rep >>
  simp[Abbr `bty`, evaluate_type_def]
  >- (disch_then (qspecl_then [`StringV s`, `sb`, `mem`] mp_tac) >>
      gvs[vyper_to_abi_base_def, value_has_type_def, val_footprint_def, enc_def]) >>
  disch_then (qspecl_then [`BytesV l`, `sb`, `mem`] mp_tac) >>
  gvs[vyper_to_abi_base_def, value_has_type_def, val_footprint_def, enc_def]
QED

Theorem abi_encode_translated_region_nonword_supplier:
  ~is_word_type ty /\ expr_val_rel cx ty v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\
  sfields_tenv_consistent sf (get_tenv cx) /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!t v. evaluate_type (get_tenv cx) t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  type_memory_bytes ce ty < dimword (:256) /\
  abi_decoder_operand_live next op /\
  (!w. eval_operand op s = SOME w ==>
    venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (lo,hi-lo)) ==>
  ?ct rv. source_rep (get_tenv cx) ty (type_to_abi_enc_info sf ce ty) ct /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) ty) av /\
    abi_encode_region_input sf ce ty ct rv op next lo hi s /\
    abi_tuple_encode_layout ce [(op,ty)] [ct]
Proof
  strip_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  simp[expr_val_rel_def] >> strip_tac >>
  `val_in_memory tv v (w2n w) s.vs_memory` by metis_tac[] >>
  `?ct rv. source_rep (get_tenv cx) ty (type_to_abi_enc_info sf ce ty) ct /\
     enc ct rv = enc (vyper_to_abi_type (get_tenv cx) ty) av /\
     abi_encoder_open_input (type_to_abi_enc_info sf ce ty) ct rv (w2n w)
       (val_footprint tv v) s.vs_memory` by
    (irule abi_encode_translated_source_footprint >> simp[] >>
     qexists `get_tenv cx` >> simp[]) >>
  `val_wf tv v` by metis_tac[cj 1 value_has_type_val_wf] >>
  drule val_footprint_le >> strip_tac >>
  `abi_embedded_static_size ce.ce_struct_fields ty =
     abi_member_head_size (vyper_to_abi_type (get_tenv cx) ty)` by
    metis_tac[abi_encode_translated_head] >>
  `is_abi_dynamic ce.ce_struct_fields ty =
     is_dynamic (vyper_to_abi_type (get_tenv cx) ty)` by
    metis_tac[abi_encode_translated_dynamic] >>
  `type_memory_bytes ce ty = type_memory_size tv` by metis_tac[] >>
  drule_all source_rep_compiler_layout >> strip_tac >>
  qexistsl [`ct`, `rv`] >> simp[] >> conj_tac
  >- (simp[abi_encode_region_input_def] >>
      qexistsl [`w2n w`, `val_footprint tv v`] >> simp[w2n_lt] >> metis_tac[]) >>
  simp[abi_tuple_encode_layout_def] >> metis_tac[]
QED

Theorem abi_encode_translated_region_supplier:
  expr_val_rel cx ty v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\
  sfields_tenv_consistent sf (get_tenv cx) /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!t v. evaluate_type (get_tenv cx) t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  type_memory_bytes ce ty < dimword (:256) /\
  abi_decoder_operand_live next op /\
  (!w. ~is_word_type ty /\ eval_operand op s = SOME w ==>
    venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (lo,hi-lo)) ==>
  ?ct rv. enc ct rv = enc (vyper_to_abi_type (get_tenv cx) ty) av /\
    abi_encode_region_input sf ce ty ct rv op next lo hi s /\
    abi_tuple_encode_layout ce [(op,ty)] [ct]
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (`~is_dynamic (vyper_to_abi_type (get_tenv cx) ty) /\ type_memory_size tv = 32` by
        metis_tac[abi_encoder_word_source_shape] >>
      `static_length (vyper_to_abi_type (get_tenv cx) ty) = 32` by
        metis_tac[abi_caller_static_memory] >>
      `abi_embedded_static_size ce.ce_struct_fields ty = 32 /\
       ~is_abi_dynamic ce.ce_struct_fields ty` by
        metis_tac[abi_encode_translated_head, abi_encode_translated_dynamic, abi_member_head_size_def] >>
      `type_memory_bytes ce ty = type_memory_size tv` by metis_tac[] >>
      drule_all abi_encode_word_zero_input_supplier >>
      simp[abi_tuple_encode_zero_input_def, abi_encode_region_input_def] >>
      metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `sfields_tenv_consistent sf _` mp_tac >> strip_tac >>
  drule_all abi_encode_translated_region_nonword_supplier >>
  metis_tac[]
QED

Theorem abi_encode_region_list_representatives:
  !xs vs avs.
  sfields_tenv_consistent sf (get_tenv cx) /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!t v. evaluate_type (get_tenv cx) t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  LENGTH xs = LENGTH vs /\
  LIST_REL (\((op,ty),v) av. ?tv.
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    vyper_to_abi (get_tenv cx) ty v = SOME av /\ expr_val_rel cx ty v op s /\
    type_memory_bytes ce ty < dimword (:256) /\ abi_decoder_operand_live next op /\
    (!w. ~is_word_type ty /\ eval_operand op s = SOME w ==>
      venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (lo,hi-lo)))
    (ZIP (xs,vs)) avs ==>
  ?cts rvs. abi_encode_region_inputs sf ce xs cts rvs next lo hi s /\
    abi_tuple_encode_layout ce xs cts /\
    LIST_REL (\(ct,rv) (bt,bv). enc ct rv = enc bt bv /\
      is_dynamic ct = is_dynamic bt /\ abi_member_head_size ct = abi_member_head_size bt)
      (ZIP (cts,rvs)) (ZIP (MAP (vyper_to_abi_type (get_tenv cx) o SND) xs,avs)) /\
    LENGTH cts = LENGTH xs /\ LENGTH rvs = LENGTH xs
Proof
  Induct >> simp[]
  >- (rpt strip_tac >> gvs[] >> simp[abi_encode_region_inputs_def, abi_tuple_encode_layout_def]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  Cases_on `vs` >> Cases_on `avs` >> gvs[] >>
  `?ct rv. enc ct rv = enc (vyper_to_abi_type (get_tenv cx) h1) h' /\
    abi_encode_region_input sf ce h1 ct rv h0 next lo hi s /\
    abi_tuple_encode_layout ce [(h0,h1)] [ct]` by
    (irule abi_encode_translated_region_supplier >> metis_tac[]) >>
  qpat_x_assum `!vs avs. _` (qspecl_then [`t`, `t'`] mp_tac) >>
  simp[] >> strip_tac >>
  `is_abi_dynamic ce.ce_struct_fields h1 = is_dynamic (vyper_to_abi_type (get_tenv cx) h1) /\
   abi_embedded_static_size ce.ce_struct_fields h1 = abi_member_head_size (vyper_to_abi_type (get_tenv cx) h1)` by
    metis_tac[abi_encode_translated_head, abi_encode_translated_dynamic] >>
  qexistsl [`ct::cts`, `rv::rvs`] >>
  gvs[abi_encode_region_inputs_def, abi_tuple_encode_layout_def]
QED

Theorem abi_encode_region_list_supplier:
  sfields_tenv_consistent sf (get_tenv cx) /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!t v. evaluate_type (get_tenv cx) t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  LENGTH xs = LENGTH vs /\
  LIST_REL (\((op,ty),v) av. ?tv.
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    vyper_to_abi (get_tenv cx) ty v = SOME av /\ expr_val_rel cx ty v op s /\
    type_memory_bytes ce ty < dimword (:256) /\ abi_decoder_operand_live next op /\
    (!w. ~is_word_type ty /\ eval_operand op s = SOME w ==>
      venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (lo,hi-lo)))
    (ZIP (xs,vs)) avs ==>
  ?cts rvs. abi_encode_region_inputs sf ce xs cts rvs next lo hi s /\
    abi_tuple_encode_layout ce xs cts /\
    enc (Tuple cts) (ListV rvs) =
      enc (Tuple (MAP (vyper_to_abi_type (get_tenv cx) o SND) xs)) (ListV avs)
Proof
  strip_tac >>
  `LENGTH xs = LENGTH avs` by
    (drule LIST_REL_LENGTH >> simp[]) >>
  qpat_x_assum `sfields_tenv_consistent sf _` mp_tac >> strip_tac >>
  drule_all abi_encode_region_list_representatives >> strip_tac >>
  qexistsl [`cts`, `rvs`] >> asm_simp_tac bool_ss [] >>
  irule abi_encode_tuple_congruence >> simp[]
QED
