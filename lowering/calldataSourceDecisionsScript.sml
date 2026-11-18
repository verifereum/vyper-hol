Theory calldataSourceDecisions
Ancestors
  calldataSourceCorrespondence vyperCalldata vyperCalldataProps
  calldataRecursiveProducers abiDecoderCoherence exprLowering abiEncoder
  compileEnv vyperValue vyperABI list arithmetic

Theorem dec_infos_need_clamp_exists:
  !infos. dec_infos_need_clamp infos =
    EXISTS (\(ei,a,m). dec_info_needs_clamp ei) infos
Proof
  Induct >> simp[dec_info_needs_clamp_def] >>
  gen_tac >> PairCases_on `h` >> simp[dec_info_needs_clamp_def]
QED

Theorem calldata_coherent_clamp:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) = tv_needs_clamp tv
Proof
  ho_match_mp_tac calldata_coherent_induction >> rpt conj_tac >>
  rpt gen_tac >> strip_tac
  >- (Cases_on `bt` >>
      gvs[type_to_abi_dec_info_def, type_to_abi_clamp_def,
          dec_info_needs_clamp_def, needs_clamp_def, tv_needs_clamp_def,
          abi_decoder_scalar_valid_def, SF boolSimps.COND_elim_ss] >>
      rename1 `BytesT b` >> Cases_on `b` >>
      gvs[type_to_abi_dec_info_def, type_to_abi_clamp_def,
          dec_info_needs_clamp_def, needs_clamp_def, tv_needs_clamp_def,
          abi_decoder_scalar_valid_def, SF boolSimps.COND_elim_ss])
  >- (simp[type_to_abi_dec_info_def, dec_info_needs_clamp_def,
           needs_clamp_def, tv_needs_clamp_def, SF boolSimps.COND_elim_ss])
  >- (Cases_on `bound` >>
      gvs[type_to_abi_dec_info_def, dec_info_needs_clamp_def,
          tv_needs_clamp_def, dec_infos_need_clamp_exists, EXISTS_GENLIST] >>
      gvs[abi_decoder_header_def, evaluate_type_def, AllCaseEqs()] >>
      metis_tac[arithmeticTheory.NOT_ZERO_LT_ZERO])
  >- (qpat_x_assum `abi_decoder_header _ _ _ _` kall_tac >>
      simp[type_to_abi_dec_info_def, dec_info_needs_clamp_def,
           dec_infos_need_clamp_exists, EXISTS_MAP, tv_needs_clamp_def,
           tv_needs_clamp_list_exists] >>
      pop_assum mp_tac >> qid_spec_tac `tvs` >> Induct_on `tys` >>
      Cases_on `tvs` >> simp[] >> metis_tac[])
  >> simp[type_to_abi_dec_info_def, dec_info_needs_clamp_def,
          dec_infos_need_clamp_exists, EXISTS_MAP, tv_needs_clamp_def,
          tv_needs_clamp_fields_map, tv_needs_clamp_list_exists]
  >> qpat_x_assum `MAP _ fields = args` (SUBST_ALL_TAC o SYM)
  >> qpat_x_assum `LIST_REL _ _ _` mp_tac
  >> rpt (pop_assum kall_tac)
  >> qid_spec_tac `tvs` >> Induct_on `fields` >> Cases_on `tvs` >> simp[]
  >> qx_gen_tac `fld` >> PairCases_on `fld` >> simp[] >> metis_tac[]
QED

Theorem calldata_coherent_offset:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  dec_info_needs_offset (type_to_abi_dec_info sf ce ty) = tv_abi_dynamic tv
Proof
  rpt gen_tac >> strip_tac >>
  drule calldata_coherent_dynamic >> disch_then (rewrite_tac o single o SYM) >>
  qpat_x_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
  rewrite_tac[Once abi_decoder_coherent_cases] >> strip_tac >> fs[]
  >- (Cases_on `bt` >>
      simp[type_to_abi_dec_info_def, dec_info_needs_offset_def, is_abi_dynamic_def] >>
      rename1 `BytesT b` >> Cases_on `b` >>
      simp[type_to_abi_dec_info_def, dec_info_needs_offset_def, is_abi_dynamic_def])
  >- simp[type_to_abi_dec_info_def, dec_info_needs_offset_def, is_abi_dynamic_def]
  >- (Cases_on `bound` >>
      gvs[type_to_abi_dec_info_def, dec_info_needs_offset_def, is_abi_dynamic_def] >>
      gvs[abi_decoder_header_def, evaluate_type_def, AllCaseEqs()] >>
      simp[GENLIST_EQ_NIL])
  >- (Cases_on `tys` >>
      simp[type_to_abi_dec_info_def, dec_info_needs_offset_def, is_abi_dynamic_def,
           SF boolSimps.ETA_ss])
  >> `LIST_REL (\ty tv. is_dynamic (vyper_to_abi_type (env \\ nsid) ty) =
          is_abi_dynamic ce.ce_struct_fields ty) (MAP SND args) tvs` by
       (gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
        first_x_assum drule >> strip_tac >>
        drule abi_decoder_coherent_header >> simp[abi_decoder_header_def])
  >> qpat_x_assum `abi_decoder_header _ _ _ _` mp_tac
  >> simp[abi_decoder_header_def, vyper_to_abi_type_def]
  >> strip_tac
  >> fs[type_to_abi_dec_info_def, dec_info_needs_offset_def]
  >> qpat_x_assum `any_dynamic _ = is_abi_dynamic _ _`
       (fn th => once_rewrite_tac[GSYM th])
  >> qpat_x_assum `MAP _ fields = args` (SUBST_ALL_TAC o SYM)
  >> qpat_x_assum `LIST_REL (\ty tv. is_dynamic _ = _) _ _` mp_tac
  >> rpt (pop_assum kall_tac)
  >> qid_spec_tac `tvs` >> Induct_on `fields` >> Cases_on `tvs` >>
     simp[vyper_to_abi_type_def, EXISTS_MAP]
  >> qx_gen_tac `fld` >> PairCases_on `fld` >>
     simp[vyper_to_abi_type_def] >> strip_tac >>
     first_x_assum (qspec_then `t` mp_tac) >>
     Cases_on `fields` >> gvs[EXISTS_MAP, vyper_to_abi_type_def]
QED
