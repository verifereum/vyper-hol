(* Recursive byte-width validity supplies ABI inhabitants, including array children. *)
Theory abiWidthInhabited
Ancestors
  abiDecoderWidthBoundary abiDecoderCoherence abiMalformedChildPremises
  abiEncoder exprLowering compileEnv vyperTypeSystem vyperValue vyperABI
  valueEncoding valueEncodingTyping valueEncodingProps contractABI
  list rich_list words arithmetic pair

Theorem abi_width_members_inhabited[local]:
  !tys tvs.
  LIST_REL (\ty tv. abi_decoder_coherent ce env sf ty tv /\
    (abi_decode_bytes_widths env ty /\ assignable_type env ty /\
     type_memory_size tv < dimword (:256) ==>
     ?a. has_type (vyper_to_abi_type env ty) a)) tys tvs /\
  EVERY (abi_decode_bytes_widths env) tys /\
  EVERY (assignable_type env) tys /\
  type_memory_size_list tvs < dimword (:256) ==>
  ?avs. has_types (vyper_to_abi_types env tys) avs /\
    LENGTH avs = LENGTH tys /\ LENGTH tys <= type_memory_size_list tvs
Proof
  Induct >> Cases_on `tvs` >> simp[has_type_def, type_memory_size_def] >>
  rpt strip_tac >> rename1 `abi_decoder_coherent ce env sf head tv` >>
  `type_memory_size tv < dimword (:256) /\
   type_memory_size_list t < dimword (:256)` by decide_tac >>
  `?a. has_type (vyper_to_abi_type env head) a` by metis_tac[] >>
  `?avs. has_types (vyper_to_abi_types env tys) avs /\
    LENGTH avs = LENGTH tys /\ LENGTH tys <= type_memory_size_list t` by metis_tac[LESS_EQ_ADD] >>
  `0 < type_memory_size tv` by
    (drule abi_decoder_coherent_header >>
     simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
     `0 < type_slot_size tv` by metis_tac[assignable_type_slot_size_pos] >>
     qspec_then `tv` mp_tac (cj 1 type_memory_size_slots) >> decide_tac) >>
  qexists_tac `a::avs` >> simp[has_type_def] >> decide_tac
QED

Theorem abi_width_coherent_inhabited:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    abi_decode_bytes_widths env ty /\ assignable_type env ty /\
    type_memory_size tv < dimword (:256) ==>
    ?av. has_type (vyper_to_abi_type env ty) av
Proof
  ho_match_mp_tac abi_decoder_coherent_strongind >> rpt conj_tac
  >- suspend "base"
  >- (rpt strip_tac >> qexists_tac `NumV 0` >>
      simp[has_type_def, valid_int_bound_def])
  >- suspend "array"
  >- suspend "tuple"
  >> suspend "struct"
QED

Resume abi_width_coherent_inhabited[base]:
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  Cases_on `is_word_type (BaseT bt)`
  >- (simp[vyper_to_abi_type_def] >> irule abi_decoder_base_width_inhabited >>
      simp[] >> qexistsl_tac [`env`, `BaseTV bt`] >> fs[abi_decoder_header_def]) >>
  Cases_on `bt` >> gvs[is_word_type_def]
  >- (qexists_tac `contractABI$BytesV []` >>
      simp[has_type_def, valid_length_def, dimword_def]) >>
  Cases_on `b` >>
  gvs[is_word_type_def, abi_decoder_scalar_valid_def] >>
  qexists_tac `contractABI$BytesV []` >>
  simp[vyper_to_abi_type_def, vyper_base_to_abi_type_def,
       has_type_def, valid_bytes_bound_def, valid_length_def, dimword_def]
QED
Resume abi_width_coherent_inhabited[array]:
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  Cases_on `bound`
  >- (rename1 `Fixed n` >> Cases_on `n`
      >- (qexists_tac `ListV []` >>
          simp[has_type_def, valid_length_def]) >>
      `abi_decode_bytes_widths env ty /\ assignable_type env ty` by
        fs[abi_decode_bytes_widths_def, assignable_type_def] >>
      `type_memory_size tv < dimword (:256)` by
        (fs[type_memory_size_def] >>
         `type_memory_size tv <= SUC n' * type_memory_size tv` by simp[] >>
         decide_tac) >>
      `?a. has_type (vyper_to_abi_type env ty) a` by metis_tac[] >>
      qexists_tac `ListV (REPLICATE (SUC n') a)` >>
      simp[has_type_def, valid_length_def] >>
      conj_tac
      >- (qsuff_tac `!n. has_types (REPLICATE n (vyper_to_abi_type env ty))
                         (REPLICATE n a)` >- simp[] >>
          qpat_x_assum `has_type _ a` mp_tac >>
          rpt (pop_assum kall_tac) >> strip_tac >>
          Induct >> simp[has_type_def]) >>
      `0 < type_slot_size tv` by
        (drule abi_decoder_coherent_header >>
         fs[abi_decoder_header_def] >> metis_tac[assignable_type_slot_size_pos]) >>
      qpat_x_assum `abi_decoder_header _ _ _ _` mp_tac >>
      simp[abi_decoder_header_def, Once evaluate_type_def,
           type_slot_size_def, AllCaseEqs()] >> rpt strip_tac >>
      `SUC n' <= SUC n' * type_slot_size tv` by simp[] >> decide_tac) >>
  qexists_tac `ListV []` >> simp[has_type_def, valid_length_def, dimword_def]
QED
Resume abi_width_coherent_inhabited[tuple]:
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  drule abi_width_members_inhabited >>
  impl_tac >- (fs[abi_decode_bytes_widths_def, assignable_type_def,
                  type_memory_size_def, EVERY_MEM] >> metis_tac[]) >>
  strip_tac >> qexists_tac `ListV avs` >> simp[has_type_def] >> fs[type_memory_size_def] >> decide_tac
QED
Resume abi_width_coherent_inhabited[struct]:
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  `LENGTH args = LENGTH tvs` by fs[LIST_REL_EL_EQN] >>
  `type_memory_size_list tvs < dimword (:256)` by
    fs[type_memory_size_def, type_memory_size_fields_zip] >>
  drule abi_width_members_inhabited >>
  impl_tac >- (fs[abi_decode_bytes_widths_def, assignable_type_def,
                  EVERY_MAP, EVERY_MEM, FORALL_PROD] >> gvs[] >> metis_tac[]) >>
  strip_tac >> qexists_tac `ListV avs` >>
  simp[Once vyper_to_abi_type_def, has_type_def] >> fs[] >> decide_tac
QED
Finalise abi_width_coherent_inhabited

Theorem abi_width_dynamic_child_inhabited:
  abi_decoder_coherent ce env sf ty tv /\
  abi_decode_bytes_widths env (ArrayT ty (Dynamic maxn)) /\
  assignable_type env (ArrayT ty (Dynamic maxn)) /\
  type_memory_size (ArrayTV tv (Dynamic maxn)) < dimword (:256) /\
  0 < maxn ==>
  abi_decode_bytes_widths env ty /\ assignable_type env ty /\
  type_memory_size tv < dimword (:256) /\
  ?av. has_type (vyper_to_abi_type env ty) av
Proof
  rpt strip_tac >>
  `assignable_type env ty /\ type_memory_size tv < dimword (:256)` by
    (irule abi_malformed_array_child_bound >>
     qexists_tac `Dynamic maxn` >> simp[]) >>
  `abi_decode_bytes_widths env ty` by fs[abi_decode_bytes_widths_def] >>
  simp[] >> irule abi_width_coherent_inhabited >> metis_tac[]
QED
