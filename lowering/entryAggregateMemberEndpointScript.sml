(* Aggregate constructors retain the endpoint of the framed tuple fold. *)
Theory entryAggregateMemberEndpoint
Ancestors
  entryTupleMemberFold entryDecoderMemberEndpoint abiDecoderValidFixed
  abiDecoderCoherence abiDecoderMemberInfos abiDecoderComplexGuard abiDecoderComplexHead
  abiDecoderValidContract abiDecoderMembers calldataSourceMemberFold
  valueEncodingProofs valueEncoding compileEnv emitHelper list arithmetic

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
