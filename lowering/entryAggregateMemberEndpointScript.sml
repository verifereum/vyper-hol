(* Aggregate constructors retain the endpoint of the framed tuple fold. *)
Theory entryAggregateMemberEndpoint
Ancestors
  entryAggregateValuePackaging abiStaticDynarrayLayout valueEncodingProps vyperTyping
  valueEncodingTyping abiDecoderFixedMemory
  entryTupleMemberFold entryDecoderMemberEndpoint abiDecoderValidFixed
  abiDecoderCoherence abiDecoderMemberInfos abiDecoderComplexGuard abiDecoderComplexHead
  abiDecoderValidContract abiDecoderMembers calldataSourceMemberFold
  valueEncodingProofs valueEncoding compileEnv emitHelper list rich_list arithmetic

Theorem entry_member_tuple_contract:
  LIST_REL (entry_member_child_contract ce env sf ctx fn site limit_st) tys tvs ==>
  entry_member_child_contract ce env sf ctx fn site limit_st (TupleT tys) (TupleTV tvs)
Proof
  strip_tac >> rewrite_tac[entry_member_child_contract_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decoder_valid_tuple_inputs >> strip_tac >>
  `LIST_REL (abi_decoder_coherent ce env sf) tys tvs` by
    (qhdtm_assum `abi_decoder_valid_pre` mp_tac >>
     simp_tac (srw_ss()) [abi_decoder_valid_pre_def, abi_decoder_coherent_tuple_iff]) >>
  `MAP type_memory_size tvs = MAP (type_memory_bytes ce) tys` by
    (qpat_assum `LIST_REL (abi_decoder_coherent _ _ _) _ _` mp_tac >>
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
  `!i. i < LENGTH tys ==> entry_member_child_contract ce env sf ctx fn site limit_st
    (EL i tys) (EL i tvs)` by
    (qpat_assum `LIST_REL (entry_member_child_contract _ _ _ _ _ _ _) _ _` mp_tac >>
     simp_tac bool_ss [LIST_REL_EL_EQN] >> metis_tac[]) >>
  `base_addr <= p /\ p + SUM (MAP type_memory_size tvs) <= base_addr + cap /\
    SUM (MAP type_memory_size tvs) <= SUM (MAP (type_memory_bytes ce) tys) /\
    p + SUM (MAP type_memory_size tvs) < dimword (:256)` by
    gvs[type_memory_size_def, type_memory_size_list_sum] >>
  drule_all (BETA_RULE (SIMP_RULE (pure_ss ++ boolSimps.LET_ss) []
    entry_source_members_tuple_success)) >> strip_tac >>
  qexistsl_tac [`t`,`scratch`] >>
  asm_simp_tac (srw_ss()) [calldata_member_success_def, type_memory_size_def,
    type_memory_size_list_sum, val_wf_def, val_in_memory_def]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag entry_member_tuple_contract)
  in if null axioms andalso null (Thm.hyp entry_member_tuple_contract) andalso
        List.all (fn tag => tag = "DISK_THM") oracles
     then () else raise Fail "tuple entry endpoint unexpected admission"
  end;

Theorem entry_member_struct_contract:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  LIST_REL (abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid))
    (MAP SND args) tvs /\
  (!i. i < LENGTH args ==> entry_member_child_contract ce (env \\ nsid)
    (sf \\ nsid_to_string nsid) ctx fn site limit_st (SND (EL i args)) (EL i tvs)) ==>
  entry_member_child_contract ce env sf ctx fn site limit_st
    (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
  strip_tac >> rewrite_tac[entry_member_child_contract_def] >>
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
    simp[type_memory_size_def, type_memory_size_fields_zip, type_memory_size_list_sum] >>
  `base_addr <= p /\
    p + SUM (MAP type_memory_size tvs) <= base_addr + cap /\
    SUM (MAP type_memory_size tvs) <= SUM (MAP (type_memory_bytes ce) (MAP SND args)) /\
    p + SUM (MAP type_memory_size tvs) < dimword (:256)` by gvs[] >>
  `!i. i < LENGTH (MAP SND args) ==> entry_member_child_contract ce
    (env \\ nsid) (sf \\ nsid_to_string nsid) ctx fn site limit_st
    (EL i (MAP SND args)) (EL i tvs)` by simp[EL_MAP] >>
  drule_all (BETA_RULE (SIMP_RULE (pure_ss ++ boolSimps.LET_ss) []
    entry_source_members_tuple_success)) >> strip_tac >>
  qexistsl_tac [`t`,`scratch`] >>
  simp_tac bool_ss [calldata_member_success_def] >> suspend "value"
QED
Resume entry_member_struct_contract[layout]:
  qpat_assum `LIST_REL _ _ _` mp_tac >> rpt (pop_assum kall_tac) >>
  simp_tac list_ss [LIST_REL_EL_EQN] >> strip_tac >>
  irule LIST_EQ >> asm_simp_tac list_ss [EL_MAP, LENGTH_MAP] >> rpt strip_tac >>
  `abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid)
    (EL x (MAP SND args)) (EL x tvs)` by metis_tac[] >>
  drule abi_decoder_coherent_header >> simp[abi_decoder_header_def, EL_MAP]
QED
Resume entry_member_struct_contract[value]:
  `val_wf (StructTV (ZIP (MAP FST args,tvs))) (StructV fields)` by
    (irule entry_fields_tuple_wf >> simp[]) >>
  `fields_in_memory fields (ZIP (MAP FST args,tvs)) p t.vs_memory` by
    (irule static_fields_memory_zip >> fs[Once value_has_type_def]) >>
  asm_simp_tac bool_ss [val_in_memory_struct]
QED
Finalise entry_member_struct_contract

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag entry_member_struct_contract)
  in if null axioms andalso null (Thm.hyp entry_member_struct_contract) andalso
        List.all (fn tag => tag = "DISK_THM") oracles
     then () else raise Fail "struct entry endpoint unexpected admission"
  end;

Theorem entry_member_fixed_contract:
  abi_decoder_coherent ce env sf ty tv /\
  entry_member_child_contract ce env sf ctx fn site limit_st ty tv ==>
  entry_member_child_contract ce env sf ctx fn site limit_st
    (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
Proof
  strip_tac >> rewrite_tac[entry_member_child_contract_def] >>
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
    entry_member_child_contract ce env sf ctx fn site limit_st
      (EL i (REPLICATE n ty)) (EL i (REPLICATE n tv))` by simp[EL_REPLICATE] >>
  `LENGTH vs = LENGTH (REPLICATE n ty)` by simp[] >>
  drule_all (BETA_RULE (SIMP_RULE (pure_ss ++ boolSimps.LET_ss) []
    entry_source_members_tuple_success)) >> strip_tac >>
  qexistsl_tac [`t`,`scratch`] >>
  `val_wf (ArrayTV tv (Fixed n))
    (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs)))` by
    (irule entry_fixed_array_wf >> simp[]) >>
  `val_in_memory (ArrayTV tv (Fixed n))
    (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))) p t.vs_memory` by
    (irule abi_decoder_fixed_array_memory >> simp[]) >>
  `SUM (MAP (type_memory_bytes ce) (REPLICATE n ty)) = n * type_memory_size tv` by
    (qpat_assum `MAP type_memory_size _ = _` (mp_tac o AP_TERM ``SUM : num list -> num``) >>
     simp_tac (srw_ss()) [map_replicate, SUM_REPLICATE] >> metis_tac[]) >>
  asm_simp_tac (srw_ss()) [calldata_member_success_def, type_memory_size_def] >>
  qhdtm_x_assum `calldata_member_resource_frame` mp_tac >>
  qpat_assum `SUM (MAP (type_memory_bytes ce) _) = _`
    (fn th => pure_rewrite_tac[th]) >> simp[]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag entry_member_fixed_contract)
  in if null axioms andalso null (Thm.hyp entry_member_fixed_contract) andalso
        List.all (fn tag => tag = "DISK_THM") oracles
     then () else raise Fail "fixed entry endpoint unexpected admission"
  end;
