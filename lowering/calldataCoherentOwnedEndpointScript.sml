(* Production adapters for the uniform coherent calldata owned endpoint. *)
Theory calldataCoherentOwnedEndpoint
Ancestors
  calldataSourceMemberFold calldataFiniteEndpoints calldataOwnedLoopClosure
  decoderEndpointComposition calldataArrayCompileBoundary abiDecoderCoherence
  calldataMemberResourceFrame allocaFrontierBound exprLowering
  valueEncoding list rich_list arithmetic abiDecoderValidFixed abiDecoderMemberInfos
  abiDecoderComplexGuard abiDecoderComplexHead abiDecoderMembers abiEncoder compileEnv

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

Theorem calldata_bulk_child_contract[local]:
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

Theorem calldata_base_child_contract[local]:
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

Theorem calldata_flag_child_contract[local]:
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

Theorem calldata_tuple_child_contract[local]:
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
