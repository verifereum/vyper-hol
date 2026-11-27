Theory bodyAbiDecodeGuardedMemberMods
Ancestors
  bodyAbiDecodeGuardedEffectBaseMods bodyFullAbiDecodeCutMember
  abiDecoderSingletonSetup bodyFullAbiDecodeCutNoncrossing
  bodyFullAbiDecodeMemberPrefix compileEnv list abiDecoderMemberInfos
  fragGasPath abiEncoder
Libs
  bodyAbiDecodeGuardedEffectSyntaxLib
  bodyFullAbiDecodeCutPathLib

val member_regular = guarded_effect_compiler_cases (guarded_effect_length_ind_typed ());
val member_crossing = guarded_effect_compiler_cases (guarded_effect_cut_ind ());
val normalize_member = CONV_TAC normalize_guarded_effect;

Theorem abi_decode_guarded_member_nil_mods:
  ^(#nil_case member_regular)
Proof
  normalize_member >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  gnvs[abiDecoderSingletonSetupTheory.abi_decode_complex_nil, comp_return_def] >>
  `tvs = []` by
    (qpat_assum `LIST_REL _ _ _` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     qpat_assum `LENGTH pretys = LENGTH pretvs` mp_tac >>
     Cases_on `tys` >> gvs[abi_decoder_member_infos_def] >>
     Cases_on `tvs` >> simp[]) >>
  qexistsl [`OK s`, `G`, `tn`] >> conj_tac
  >- (rpt strip_tac >> irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule (cj 1 gas_path_rules) >> simp[]) >>
  disj1_tac >> qexists `s` >> simp[abi_decode_guarded_effect_refl_core] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_decode_guarded_member_nil_cut_mods:
  ^(#nil_case member_crossing)
Proof
  normalize_member >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ [] _ _ _ = _` mp_tac >>
  simp[Once compile_abi_decode_to_buf_def, comp_return_def] >> metis_tac[]
QED
