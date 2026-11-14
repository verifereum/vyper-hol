Theory abiUnclampedInhabited
Ancestors
  abiDecoderWidthBoundary abiMalformedStaticReflection abiDecoderCoherence
  exprLowering abiEncoder compileEnv vyperABI vyperValue contractABI list rich_list words
  vyperTypeSystem valueEncodingProps valueEncoding valueEncodingTyping pair abiDecoderMembers

Theorem abi_dec_infos_map_clamp[local]:
  !xs. dec_infos_need_clamp (MAP f xs) =
       EXISTS (\x. dec_info_needs_clamp (FST (f x))) xs
Proof
  Induct >> simp[dec_info_needs_clamp_def] >>
  Cases_on `f h` >> Cases_on `r` >> simp[dec_info_needs_clamp_def]
QED

Theorem abi_types_witness[local]:
  !tys. EVERY (\ty. ?a. has_type (vyper_to_abi_type env ty) a) tys ==>
    ?avs. has_types (vyper_to_abi_types env tys) avs /\ LENGTH avs = LENGTH tys
Proof
  Induct
  >- (strip_tac >> qexists_tac `[]` >> simp[has_type_def]) >>
  simp[] >> rpt strip_tac >>
  `?avs. has_types (vyper_to_abi_types env tys) avs /\ LENGTH avs = LENGTH tys` by metis_tac[] >>
  qexists_tac `a::avs` >> simp[has_type_def]
QED

Theorem abi_has_types_replicate[local]:
  !n. has_type ty a ==> has_types (REPLICATE n ty) (REPLICATE n a)
Proof
  Induct >> simp[has_type_def]
QED

Theorem abi_memory_member_bound[local]:
  !tvs tv. MEM tv tvs ==> type_memory_size tv <= type_memory_size_list tvs
Proof
  Induct >> simp[type_memory_size_def] >> rpt strip_tac >> gvs[] >>
  res_tac >> decide_tac
QED

Theorem abi_memory_list_count[local]:
  !tvs. EVERY (\tv. 0 < type_memory_size tv) tvs ==>
    LENGTH tvs <= type_memory_size_list tvs
Proof
  Induct >> simp[type_memory_size_def] >> rpt strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem abi_static_members_witness[local]:
  !ce env sf tys tvs.
  LIST_REL (\ty tv. abi_decoder_coherent ce env sf ty tv /\
    (assignable_type env ty /\ type_memory_size tv < dimword (:256) /\
     ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
     ~is_abi_dynamic ce.ce_struct_fields ty ==>
     ?a. has_type (vyper_to_abi_type env ty) a)) tys tvs /\
  EVERY (assignable_type env) tys /\
  EVERY (\ty. ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) tys /\
  EVERY (\ty. ~is_abi_dynamic ce.ce_struct_fields ty) tys /\
  type_memory_size_list tvs < dimword (:256) ==>
  ?avs. has_types (vyper_to_abi_types env tys) avs /\ LENGTH avs < dimword (:256)
Proof
  rpt strip_tac >>
  `EVERY (\ty. ?a. has_type (vyper_to_abi_type env ty) a) tys` by
    (gvs[LIST_REL_EL_EQN, EVERY_EL] >> rpt strip_tac >>
     `type_memory_size (EL n tvs) <= type_memory_size_list tvs` by
       (irule abi_memory_member_bound >> simp[EL_MEM]) >>
     `type_memory_size (EL n tvs) < dimword (:256)` by decide_tac >>
     metis_tac[]) >>
  drule abi_types_witness >> strip_tac >> qexists_tac `avs` >> simp[] >>
  `EVERY (\tv. 0 < type_memory_size tv) tvs` by
    (gvs[LIST_REL_EL_EQN, EVERY_EL] >> rpt strip_tac >>
     `abi_decoder_coherent ce env sf (EL n tys) (EL n tvs)` by metis_tac[] >>
     drule abi_decoder_coherent_header >>
     rewrite_tac[abi_decoder_header_def] >> strip_tac >>
     `assignable_type env (EL n tys)` by metis_tac[] >>
     `0 < type_slot_size (EL n tvs)` by metis_tac[assignable_type_slot_size_pos] >>
     pure_rewrite_tac[type_memory_size_slots] >> decide_tac) >>
  drule abi_memory_list_count >> fs[LIST_REL_EL_EQN]
QED

Theorem abi_unclamped_static_inhabited:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    assignable_type env ty /\ type_memory_size tv < dimword (:256) /\
    ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
    ~is_abi_dynamic ce.ce_struct_fields ty ==>
    ?a. has_type (vyper_to_abi_type env ty) a
Proof
  ho_match_mp_tac abi_decoder_coherent_strongind >> rpt conj_tac
  >- suspend "base"
  >- (rpt strip_tac >> qexists_tac `NumV 0` >>
      simp[has_type_def, valid_int_bound_def])
  >- suspend "array"
  >- suspend "tuple"
  >> suspend "struct"
QED

Resume abi_unclamped_static_inhabited[base]:
  rpt gen_tac >> strip_tac >> Cases_on `bt` >>
  simp[type_to_abi_dec_info_def, type_to_abi_clamp_def,
       dec_info_needs_clamp_def, needs_clamp_def] >>
  rpt strip_tac >>
  gvs[abi_decoder_scalar_valid_def] >>
  FIRST [
    (Cases_on `n = 256` >> gvs[needs_clamp_def] >>
     FIRST [(qexists_tac `NumV 0` >> simp[has_type_def, valid_int_bound_def] >> NO_TAC),
       (qexists_tac `contractABI$IntV 0` >> simp[has_type_def, valid_int_bound_def, int_bits_bound_def] >> NO_TAC)] >> NO_TAC),
    (qexists_tac `NumV 0` >> simp[has_type_def, valid_int_bound_def] >> NO_TAC),
    (qexists_tac `contractABI$IntV 0` >>
      simp[has_type_def, valid_int_bound_def, int_bits_bound_def] >> NO_TAC),
    (Cases_on `b` >>
     gvs[type_to_abi_dec_info_def, type_to_abi_clamp_def,
         dec_info_needs_clamp_def, needs_clamp_def, AllCaseEqs()] >>
     Cases_on `n = 32` >> gvs[needs_clamp_def] >>
     qexists_tac `contractABI$BytesV (REPLICATE 32 0w)` >>
     simp[has_type_def, valid_bytes_bound_def, valid_length_def, dimword_def]) ]
QED
Resume abi_unclamped_static_inhabited[array]:
  rpt gen_tac >> strip_tac >> Cases_on `bound` >>
  simp[type_to_abi_dec_info_def, dec_info_needs_clamp_def] >>
  strip_tac >> rename1 `Fixed n` >> Cases_on `n`
  >- (qexists_tac `ListV []` >> simp[has_type_def, valid_length_def]) >>
  gvs[GENLIST_CONS, dec_info_needs_clamp_def] >>
  `~is_abi_dynamic ce.ce_struct_fields ty` by
    (drule abi_decoder_coherent_header >>
     fs[abi_decoder_header_def, is_dynamic_def]) >>
  `assignable_type env ty` by fs[assignable_type_def] >>
  `type_memory_size tv < dimword (:256)` by
    (fs[type_memory_size_def] >>
     `type_memory_size tv <= SUC n' * type_memory_size tv` by simp[] >>
     decide_tac) >>
  `?a. has_type (vyper_to_abi_type env ty) a` by metis_tac[] >>
  qexists_tac `ListV (REPLICATE (SUC n') a)` >>
  simp[has_type_def, valid_length_def, abi_has_types_replicate] >>
  qpat_x_assum `abi_decoder_header _ _ _ _` mp_tac >>
  simp[abi_decoder_header_def, Once evaluate_type_def,
       type_slot_size_def, AllCaseEqs()] >>
  rpt strip_tac >>
  `SUC n' <= SUC n' * type_slot_size tv` by simp[] >> decide_tac
QED
Resume abi_unclamped_static_inhabited[tuple]:
  rpt gen_tac >> strip_tac >>
  simp[type_to_abi_dec_info_def, dec_info_needs_clamp_def,
       abi_dec_infos_map_clamp] >> strip_tac >>
  drule abi_static_members_witness >>
  impl_tac >- (fs[assignable_type_def, is_abi_dynamic_def,
                 type_memory_size_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  strip_tac >> qexists_tac `ListV avs` >> simp[has_type_def]
QED
Resume abi_unclamped_static_inhabited[struct]:
  rpt gen_tac >> strip_tac >>
  simp[type_to_abi_dec_info_def, dec_info_needs_clamp_def,
       assignable_type_def] >> strip_tac >>
  `LENGTH args = LENGTH tvs` by fs[LIST_REL_EL_EQN] >>
  `type_memory_size_list tvs < dimword (:256)` by
    (fs[type_memory_size_def, type_memory_size_fields_zip]) >>
  drule abi_static_members_witness >>
  impl_tac >- (simp[EVERY_MAP] >> conj_tac
    >- fs[combinTheory.o_DEF] >> conj_tac
    >- (qpat_x_assum `MAP _ fields = args` (SUBST1_TAC o SYM) >>
        fs[abi_dec_infos_map_clamp, EVERY_MAP, EVERY_MEM, EXISTS_MEM,
           FORALL_PROD] >> metis_tac[]) >>
    `~is_dynamic (vyper_to_abi_type env (StructT nsid))` by
      metis_tac[abi_decoder_header_def] >>
    fs[Once vyper_to_abi_type_def, is_dynamic_def,
       vyper_to_abi_types_MAP, EXISTS_MAP, EXISTS_MEM] >>
    gs[is_dynamic_def, any_dynamic_EXISTS, EXISTS_MAP, EXISTS_MEM] >>
    fs[EVERY_EL, LIST_REL_EL_EQN] >> rpt strip_tac >>
    `abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid)
       (SND (EL n args)) (EL n tvs)` by metis_tac[EL_MAP] >>
    drule abi_decoder_coherent_header >>
    rewrite_tac[abi_decoder_header_def] >> strip_tac >>
    `MEM (EL n args) args` by simp[EL_MEM] >>
    metis_tac[]) >>
  strip_tac >> qexists_tac `ListV avs` >> simp[has_type_def]
QED
Finalise abi_unclamped_static_inhabited
