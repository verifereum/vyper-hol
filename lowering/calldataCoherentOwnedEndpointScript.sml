(* Production adapters for the uniform coherent calldata owned endpoint. *)
Theory calldataCoherentOwnedEndpoint
Ancestors
  calldataSourceMemberFold calldataFiniteEndpoints calldataOwnedLoopClosure
  decoderEndpointComposition calldataArrayCompileBoundary abiDecoderCoherence
  calldataMemberResourceFrame allocaFrontierBound exprLowering abiDecoderValidArrayEntry
  vyperABI abiDecoderOffset abiDecoderEmpty abiDecoderGuard
  valueEncoding list rich_list arithmetic abiDecoderValidFixed abiDecoderMemberInfos
  abiDecoderComplexGuard abiDecoderComplexHead abiDecoderMembers abiEncoder compileEnv
  valueEncodingTyping valueEncodingProps abiStaticDynarrayLayout vyperTyping abiDecoderFixedMemory abiDecoderValidContract abiDecoderTypedContract

Theorem calldata_word_child_contract[local]:
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
  calldata_member_child_contract ce env sf ctx fn site limit_st ty tv
Proof
  strip_tac >> rewrite_tac[calldata_member_child_contract_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (BETA_RULE (REWRITE_RULE [GSYM calldata_member_own_def]
    (SIMP_RULE (pure_ss ++ boolSimps.LET_ss) [] calldata_valid_word_owned_endpoint))) >>
  strip_tac >> qexistsl_tac [`child`,`[]`] >>
  simp[calldata_member_success_def, calldata_member_resource_frame_def,
    calldata_member_wit_def, calldata_member_transfers_def]
QED

Theorem calldata_bytes_child_contract[local]:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) ==>
  calldata_member_child_contract ce env sf ctx fn site limit_st ty tv
Proof
  disch_tac >> rewrite_tac[calldata_member_child_contract_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (BETA_RULE (REWRITE_RULE [GSYM calldata_member_own_def]
    (SIMP_RULE (pure_ss ++ boolSimps.LET_ss) [] calldata_valid_bytes_owned_endpoint))) >>
  strip_tac >> qexistsl_tac [`child`,`[]`] >>
  simp[calldata_member_success_def, calldata_member_resource_frame_def,
    calldata_member_wit_def, calldata_member_transfers_def]
QED

Theorem calldata_bulk_child_contract:
  unit_alloca_budget ctx < dimword (:256) /\
  abi_decoder_header ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei ==>
  calldata_member_child_contract ce env sf ctx fn site limit_st
    (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  strip_tac >> rewrite_tac[calldata_member_child_contract_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `s.vs_alloca_next < dimword (:256)` by
    (qpat_assum `alloca_frontier_inv _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [alloca_frontier_inv_def]) >>
     decide_tac) >>
  `type_memory_bytes ce (ArrayT ty (Dynamic maxn)) =
    type_memory_size (ArrayTV tv (Dynamic maxn))` by
    fs[abi_decoder_header_def] >>
  `p + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= base_addr + cap` by simp[] >>
  drule_all (BETA_RULE (REWRITE_RULE [GSYM calldata_member_own_def]
    (SIMP_RULE (pure_ss ++ boolSimps.LET_ss) [] calldata_valid_bulk_owned_endpoint))) >>
  strip_tac >> qexistsl_tac [`child`,`[]`] >>
  simp[calldata_member_success_def, calldata_member_resource_frame_def,
    calldata_member_wit_def, calldata_member_transfers_def] >>
  qpat_x_assum `abi_decode_footprint_frame _ _ _` mp_tac >>
  asm_rewrite_tac[]
QED

Theorem calldata_base_child_contract:
  calldata_member_child_contract ce env sf ctx fn site limit_st (BaseT bt) (BaseTV bt)
Proof
  Cases_on `bt`
  >~ [`BaseT (BytesT bound)`]
  >- (Cases_on `bound`
      >- (irule calldata_word_child_contract >> simp[Once type_to_abi_dec_info_def]) >>
      irule calldata_bytes_child_contract >> simp[])
  >~ [`BaseT (StringT n)`]
  >- (irule calldata_bytes_child_contract >> simp[]) >>
  irule calldata_word_child_contract >> simp[Once type_to_abi_dec_info_def]
QED

Theorem calldata_flag_child_contract:
  calldata_member_child_contract ce env sf ctx fn site limit_st (FlagT nsid) (FlagTV n)
Proof
  irule calldata_word_child_contract >> simp[Once type_to_abi_dec_info_def]
QED

Theorem calldata_tuple_value_from_members[local]:
  !vs tvs d.
    LENGTH vs = LENGTH tvs /\
    EVERY (\i. val_wf (EL i tvs) (EL i vs) /\
      val_in_memory (EL i tvs) (EL i vs)
        (d + SUM (MAP type_memory_size (TAKE i tvs))) mem)
      (GENLIST I (LENGTH tvs)) ==>
    val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) d mem
Proof
  Induct >> Cases_on `tvs`
  >- simp[val_wf_def, val_in_memory_def]
  >- simp[]
  >- simp[] >>
  simp_tac (srw_ss()) [LENGTH, EVERY_GENLIST] >> rpt strip_tac >>
  `!i. i < LENGTH t ==> val_wf (EL i t) (EL i vs) /\
    val_in_memory (EL i t) (EL i vs)
      (d + type_memory_size h + SUM (MAP type_memory_size (TAKE i t))) mem` by
    (qpat_x_assum `!tvs d. _` kall_tac >>
     rpt strip_tac >> qpat_x_assum `!i. i < SUC _ ==> _`
      (qspec_then `SUC i` mp_tac) >>
      pure_rewrite_tac [EL, TAKE_def, MAP, SUM, ADD_ASSOC] >>
      asm_simp_tac arith_ss [TL, MAP, SUM]) >>
  first_x_assum (qspecl_then [`t`,`d+type_memory_size h`] mp_tac) >>
  simp[EVERY_GENLIST] >> strip_tac >>
  qpat_x_assum `!i. i < SUC _ ==> _` (qspec_then `0` mp_tac) >>
  gvs[val_wf_def, val_in_memory_def]
QED

Theorem calldata_tuple_child_contract:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  (!i. i < LENGTH tys ==> calldata_member_child_contract ce env sf ctx fn site limit_st
    (EL i tys) (EL i tvs)) ==>
  calldata_member_child_contract ce env sf ctx fn site limit_st (TupleT tys) (TupleTV tvs)
Proof
  strip_tac >> rewrite_tac[calldata_member_child_contract_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decoder_valid_tuple_inputs >> strip_tac >>
  `MAP type_memory_size tvs = MAP (type_memory_bytes ce) tys` by
    (qpat_assum `LIST_REL _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp_tac list_ss [LIST_REL_EL_EQN] >> strip_tac >>
     irule LIST_EQ >> asm_simp_tac list_ss [EL_MAP, LENGTH_MAP] >> rpt strip_tac >>
     `abi_decoder_coherent ce env sf (EL x tys) (EL x tvs)` by metis_tac[] >>
     drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  `compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
    (abi_decoder_member_infos sf ce tys) 0 0 first = ((),last)` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decoder_tuple_infos, abi_decode_complex_phases,
       abi_decode_complex_head_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def]) >>
  `LENGTH vs = LENGTH tys` by
    (drule abi_decoder_members_relations >> strip_tac >>
     qpat_assum `LIST_REL (abi_decoder_coherent _ _ _) _ _` mp_tac >>
     fs[LIST_REL_EL_EQN]) >>
  `base_addr <= p /\ p + SUM (MAP type_memory_size tvs) <= base_addr + cap /\
    SUM (MAP type_memory_size tvs) <= SUM (MAP (type_memory_bytes ce) tys) /\
    p + SUM (MAP type_memory_size tvs) < dimword (:256)` by
    (drule abi_decoder_member_infos_layout >> strip_tac >>
     gvs[type_memory_size_def]) >>
  drule_all (BETA_RULE (SIMP_RULE (pure_ss ++ boolSimps.LET_ss) []
    calldata_source_members_owned_success)) >>
  strip_tac >> qexistsl_tac [`t`,`scratch`] >>
  simp_tac bool_ss [calldata_member_success_def] >>
  `LENGTH vs = LENGTH tvs` by fs[LIST_REL_EL_EQN] >>
  drule_all calldata_tuple_value_from_members >> strip_tac >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  asm_simp_tac bool_ss [type_memory_size_def]
QED

Theorem calldata_struct_child_contract:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  LIST_REL (abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid))
    (MAP SND args) tvs /\
  (!i. i < LENGTH args ==> calldata_member_child_contract ce (env \\ nsid)
    (sf \\ nsid_to_string nsid) ctx fn site limit_st (SND (EL i args)) (EL i tvs)) ==>
  calldata_member_child_contract ce env sf ctx fn site limit_st
    (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
  strip_tac >> rewrite_tac[calldata_member_child_contract_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH tvs = LENGTH args` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  drule_all abi_decoder_valid_struct_inputs >> strip_tac >>
  `MAP type_memory_size tvs = MAP (type_memory_bytes ce) (MAP SND args)` by
    suspend "layout" >>
  `compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
    (abi_decoder_member_infos (sf \\ nsid_to_string nsid) ce (MAP SND args))
    0 0 first = ((),last)` by
    (drule abi_decoder_struct_infos >> strip_tac >>
     qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac std_ss [LET_THM, abi_decode_complex_phases,
       abi_decode_complex_head_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def]) >>
  `LENGTH (MAP SND fields) = LENGTH (MAP SND args)` by
    (drule abi_decoder_members_relations >> simp[LIST_REL_EL_EQN] >> metis_tac[]) >>
  `type_memory_size (StructTV (ZIP (MAP FST args,tvs))) =
    SUM (MAP (type_memory_bytes ce) (MAP SND args))` by
    (drule abi_decoder_member_infos_layout >> strip_tac >>
     simp[type_memory_size_def, type_memory_size_fields_zip]) >>
  `base_addr <= p /\
    p + SUM (MAP type_memory_size tvs) <= base_addr + cap /\
    SUM (MAP type_memory_size tvs) <= SUM (MAP (type_memory_bytes ce) (MAP SND args)) /\
    p + SUM (MAP type_memory_size tvs) < dimword (:256)` by gvs[] >>
  `!i. i < LENGTH (MAP SND args) ==> calldata_member_child_contract ce
    (env \\ nsid) (sf \\ nsid_to_string nsid) ctx fn site limit_st
    (EL i (MAP SND args)) (EL i tvs)` by simp[EL_MAP] >>
  drule_all (BETA_RULE (SIMP_RULE (pure_ss ++ boolSimps.LET_ss) []
    calldata_source_members_owned_success)) >>
  strip_tac >> qexistsl_tac [`t`,`scratch`] >>
  simp_tac bool_ss [calldata_member_success_def] >> suspend "value"
QED
Resume calldata_struct_child_contract[layout]:
  qpat_assum `LIST_REL _ _ _` mp_tac >> rpt (pop_assum kall_tac) >>
  simp_tac list_ss [LIST_REL_EL_EQN] >> strip_tac >>
  irule LIST_EQ >> asm_simp_tac list_ss [EL_MAP, LENGTH_MAP] >> rpt strip_tac >>
  `abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid)
    (EL x (MAP SND args)) (EL x tvs)` by metis_tac[] >>
  drule abi_decoder_coherent_header >> simp[abi_decoder_header_def, EL_MAP]
QED
Resume calldata_struct_child_contract[value]:
  `LENGTH (MAP SND fields) = LENGTH tvs` by simp[] >>
  drule_all calldata_tuple_value_from_members >> strip_tac >>
  `tuple_in_memory (MAP SND fields) tvs p t.vs_memory` by
    fs[val_in_memory_tuple] >>
  `fields_in_memory fields (ZIP (MAP FST args,tvs)) p t.vs_memory` by
    (irule static_fields_memory_zip >> fs[Once value_has_type_def]) >>
  `val_wf (StructTV (ZIP (MAP FST args,tvs))) v` by
    metis_tac[value_has_type_val_wf] >>
  asm_simp_tac bool_ss [val_in_memory_struct]
QED
Finalise calldata_struct_child_contract

Theorem calldata_fixed_child_contract:
  abi_decoder_coherent ce env sf ty tv /\
  calldata_member_child_contract ce env sf ctx fn site limit_st ty tv ==>
  calldata_member_child_contract ce env sf ctx fn site limit_st
    (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
Proof
  strip_tac >> rewrite_tac[calldata_member_child_contract_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decoder_valid_fixed_array_inputs >> strip_tac >>
  `LIST_REL (abi_decoder_coherent ce env sf) (REPLICATE n ty) (REPLICATE n tv)` by
    simp[LIST_REL_REPLICATE_same] >>
  `MAP type_memory_size (REPLICATE n tv) =
    MAP (type_memory_bytes ce) (REPLICATE n ty)` by
    (drule abi_decoder_coherent_header >> simp[abi_decoder_header_def, map_replicate]) >>
  `compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
    (abi_decoder_member_infos sf ce (REPLICATE n ty)) 0 0 first = ((),last)` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decoder_fixed_array_infos, abi_decode_complex_phases,
       abi_decode_complex_head_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def]) >>
  `base_addr <= p /\
    p + SUM (MAP type_memory_size (REPLICATE n tv)) <= base_addr + cap /\
    SUM (MAP type_memory_size (REPLICATE n tv)) <=
      SUM (MAP (type_memory_bytes ce) (REPLICATE n ty)) /\
    p + SUM (MAP type_memory_size (REPLICATE n tv)) < dimword (:256)` by
    (drule abi_decoder_coherent_header >>
     simp[abi_decoder_header_def] >> strip_tac >>
     gvs[type_memory_size_def, map_replicate, SUM_REPLICATE]) >>
  `!i. i < LENGTH (REPLICATE n ty) ==>
    calldata_member_child_contract ce env sf ctx fn site limit_st
      (EL i (REPLICATE n ty)) (EL i (REPLICATE n tv))` by simp[EL_REPLICATE] >>
  `LENGTH vs = LENGTH (REPLICATE n ty)` by simp[] >>
  drule_all (BETA_RULE (SIMP_RULE (pure_ss ++ boolSimps.LET_ss) []
    calldata_source_members_owned_success)) >>
  strip_tac >> qexistsl_tac [`t`,`scratch`] >>
  simp_tac bool_ss [calldata_member_success_def] >> suspend "value"
QED
Resume calldata_fixed_child_contract[value]:
  `LENGTH vs = LENGTH (REPLICATE n tv)` by simp[] >>
  drule_all calldata_tuple_value_from_members >> strip_tac >>
  `tuple_in_memory vs (REPLICATE n tv) p t.vs_memory` by
    fs[val_in_memory_tuple] >>
  `val_in_memory (ArrayTV tv (Fixed n))
    (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))) p t.vs_memory` by
    (irule abi_decoder_fixed_array_memory >> simp[]) >>
  `val_wf (ArrayTV tv (Fixed n)) v` by
    (qpat_assum `abi_decoder_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp_tac bool_ss [abi_decoder_valid_pre_def, abi_decoder_metadata_def] >>
     metis_tac[value_has_type_val_wf]) >>
  `SUM (MAP (type_memory_bytes ce) (REPLICATE n ty)) = n * type_memory_size tv` by
    (qpat_x_assum `MAP type_memory_size _ = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[map_replicate, SUM_REPLICATE]) >>
  asm_simp_tac bool_ss [type_memory_size_def] >>
  qpat_x_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  asm_simp_tac bool_ss []
QED
Finalise calldata_fixed_child_contract

(* Instantiate the recursive child once at the actual loop setup endpoint. *)
Theorem calldata_array_child_success:
  calldata_member_child_contract ce env sf ctx fn site limit_st ty tv /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) ready = ((),last) /\
  fn_has_code ready last fn /\
  (ready.cs_blocks = last.cs_blocks \/
    !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  last.cs_next_var <= limit_st.cs_next_var /\
  (oid < ready.cs_next_id \/ last.cs_next_id <= oid) /\
  type_memory_bytes ce ty = type_memory_size tv /\
  base_addr <= d+32+j*type_memory_size tv /\
  d+32+j*type_memory_size tv+type_memory_size tv <= base_addr+cap /\
  d+32+j*type_memory_size tv+type_memory_size tv < dimword (:256) /\
  abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
    (Lit 0w) sb d b reserve_cap next limit_st head entry /\
  alloca_inv entry /\ alloca_frontier_inv ctx fn site entry /\
  calldata_member_own fn ready.cs_next_id last.cs_next_id entry /\
  FLOOKUP entry.vs_allocas oid = SOME (base_addr,cap) /\
  ~entry.vs_halted /\ entry.vs_current_bb = ready.cs_current_bb /\
  entry.vs_inst_idx = LENGTH ready.cs_current_insts ==>
  ?child scratch.
    calldata_member_success ctx fn site limit_st ready last
      (d+32+j*type_memory_size tv) (type_memory_size tv) tv (EL j vs)
      entry child scratch
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_decoder_valid_array_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (pure_ss ++ boolSimps.LET_ss)
      [abi_decoder_valid_array_entry_def]) >>
  qpat_assum `type_memory_bytes ce ty = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  drule_all calldata_member_child_contract_apply >> simp[]
QED

Theorem calldata_zero_array_translation[local]:
  vyper_to_abi_type env ty = Array (SOME 0) aty ==>
  ?elem. ty = ArrayT elem (Fixed 0)
Proof
  Cases_on `ty` >> simp[Once vyper_to_abi_type_def]
  >- (Cases_on `b` >> simp[vyper_base_to_abi_type_def] >>
      rename1 `BytesT bound` >> Cases_on `bound` >> simp[vyper_base_to_abi_type_def])
  >- (rename1 `ArrayT elem bound` >> Cases_on `bound` >> simp[])
  >> Cases_on `FLOOKUP env p` >> simp[] >> Cases_on `x` >> simp[]
QED

Theorem calldata_dynamic_array_child_admissible:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    di av (ArrayV (DynArrayV vs)) /\
  is_abi_dynamic ce.ce_struct_fields ty /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) ready = ((),st1) ==>
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) \/
  (type_to_abi_dec_info sf ce ty = DecComplex T [] /\ ready = st1 /\
   EVERY (value_has_type tv) vs)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem` >> simp[] >>
  gvs[] >> drule calldata_zero_array_translation >> strip_tac >>
  gvs[is_abi_dynamic_def] >>
  rename1 `is_abi_dynamic ce.ce_struct_fields ety` >>
  `type_to_abi_dec_info sf ce (ArrayT ety (Fixed 0)) = DecComplex T []` by
    simp[abi_decoder_empty_dynamic_translation] >>
  `ready = st1` by
    gvs[abi_decode_empty_complex_phases, abi_decode_complex_head_guard_def,
      abi_decode_le_guard_def, comp_return_def] >>
  fs[abi_decoder_metadata_def, value_has_type_def, all_have_type_EVERY]
QED

Theorem calldata_static_clamped_child_exclusion:
  ~is_abi_dynamic ce.ce_struct_fields ty /\
  dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) ==>
  !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem
Proof
  rpt strip_tac >> drule calldata_zero_array_translation >> strip_tac >>
  gvs[is_abi_dynamic_def, Once type_to_abi_dec_info_def, dec_info_needs_clamp_def]
QED
