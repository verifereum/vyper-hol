(* Bounded recursive contracts specialized for the existing member fold. *)
Theory abiMalformedBoundedParents
Ancestors
  abiMalformedBoundedContract abiMalformedParentAggregate
  abiMalformedMembersFold abiMalformedMembers abiMalformedConstructorInduction
  abiDecoderCoherence abiDecoderMemberInfos abiVyperAdmissible
  abiMalformedConstructorContract abiMalformedRecursiveInterface fragExec
  vyperTypeSystem vyperValue abiDecoderMembers valueEncodingTyping
  abiValidAggregateHeads vyperABIValid
  compileEnv vyperABI contractABI valueEncoding abiValidMembers abiDecodeRanges words list rich_list arithmetic

Theorem abi_malformed_bounded_specialize:
  abi_malformed_bounded_type_contract ce env sf ty tv /\
  abi_size_bound sf ty < dimword (:256) ==>
  abi_malformed_type_contract ce env sf ty tv
Proof
  simp[abi_malformed_bounded_type_contract_def, abi_malformed_type_contract_def]
QED

Theorem abi_malformed_bounded_members:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL (abi_malformed_bounded_type_contract ce env sf) tys tvs /\
  EVERY (\ty. abi_size_bound sf ty < dimword (:256)) tys ==>
  abi_malformed_members_contract ce env sf tys tvs
Proof
  strip_tac >> irule abi_malformed_members_fold >> simp[] >>
  fs[LIST_REL_EL_EQN, EVERY_EL] >> rpt strip_tac >>
  irule abi_malformed_bounded_specialize >> metis_tac[]
QED

Theorem abi_malformed_static_members_trim:
  !ats origin other hds k.
    ~any_dynamic ats /\ SUM (MAP static_length ats) <= k ==>
    (vyper_decode_valid_enc_tuple ats origin (TAKE k hds) <=>
       vyper_decode_valid_enc_tuple ats other hds) /\
    abi_decode_members ats origin (TAKE k hds) = abi_decode_members ats other hds
Proof
  Induct >- simp[vyper_decode_valid_enc_def, abi_decode_members_def] >>
  rpt gen_tac >> simp[] >> strip_tac >>
  `static_length h <= k` by decide_tac >>
  first_x_assum (qspecl_then [`origin`, `other`, `DROP (static_length h) hds`,
     `k - static_length h`] mp_tac) >>
  simp[] >> strip_tac >>
  `MIN (static_length h) k = static_length h` by simp[MIN_DEF] >>
  simp[vyper_decode_valid_enc_def, abi_decode_members_def,
       abi_decode_member_bytes_def, abi_member_head_size_def,
       TAKE_TAKE_MIN, DROP_TAKE, LENGTH_TAKE_EQ] >>
  Cases_on `k <= LENGTH hds` >> simp[MIN_DEF] >> decide_tac
QED

Theorem abi_malformed_inhabited_members[local]:
  !tys vs. has_types (vyper_to_abi_types env tys) vs ==>
    EVERY (\ty. ?av. has_type (vyper_to_abi_type env ty) av) tys
Proof
  Induct >> Cases_on `vs` >> simp[has_type_def] >> metis_tac[]
QED

Theorem abi_malformed_bounded_tuple_contract:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL (abi_malformed_bounded_type_contract ce env sf) tys tvs /\
  abi_decoder_header ce env (TupleT tys) (TupleTV tvs) ==>
  abi_malformed_bounded_type_contract ce env sf (TupleT tys) (TupleTV tvs)
Proof
  strip_tac >> simp_tac bool_ss [abi_malformed_bounded_type_contract_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all abi_malformed_tuple_capacity >> strip_tac >>
  `abi_malformed_members_contract ce env sf tys tvs` by
    (irule abi_malformed_bounded_members >> simp[]) >>
  `EVERY (assignable_type env) tys /\
   type_memory_size_list tvs < dimword (:256) /\
   type_memory_size_list tvs <= outsz` by
    fs[assignable_type_def, type_memory_size_def, abi_decoder_header_def, SF ETA_ss] >>
  `EVERY (\ty. ?av. has_type (vyper_to_abi_type env ty) av) tys` by
    (Cases_on `av` >> fs[has_type_def] >>
     drule abi_malformed_inhabited_members >> simp[]) >>
  gvs[abi_decoder_tuple_infos] >>
  simp_tac bool_ss [abi_malformed_constructor_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  irule frag_exec_pointwise >> gen_tac >>
  disch_then (strip_assume_tac o BETA_RULE) >> gvs[] >>
  irule frag_exec_conseq >>
  drule_all abi_malformed_aggregate_fragment >>
  disch_then (irule_at Any) >> simp[] >>
  rpt strip_tac >> simp[abi_malformed_reflected_post_def] >>
  `LENGTH tys < dimword (:256)` by
    (Cases_on `av` >> fs[has_type_def] >> drule has_types_length >> simp[vyper_to_abi_types_MAP]) >>
  Cases_on `any_dynamic (vyper_to_abi_types env tys)`
  >- (simp[Once vyper_decode_valid_enc_def, vyper_to_abi_types_MAP,
           abi_decode_members_value] >> irule abiVyperAdmissibleTheory.tuple >> simp[]) >>
  `SUM (MAP static_length (vyper_to_abi_types env tys)) =
    static_length (Tuple (vyper_to_abi_types env tys))` by
    simp[static_length_Tuple_SUM] >>
  qspec_then `vyper_to_abi_types env tys` mp_tac abi_malformed_static_members_trim >>
  disch_then (qspecl_then
    [`TAKE (static_length (Tuple (vyper_to_abi_types env tys))) (DROP p xs)`,
     `DROP p xs`, `DROP p xs`,
     `static_length (Tuple (vyper_to_abi_types env tys))`] mp_tac) >>
  simp[vyper_to_abi_types_MAP] >> strip_tac >>
  simp[Once vyper_decode_valid_enc_def, vyper_to_abi_types_MAP,
       abi_decode_members_value] >> irule abiVyperAdmissibleTheory.tuple >> simp[]
QED

Theorem abi_malformed_bounded_struct_contract:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
  MAP (\(name,ty,sz). (name,ty)) fields = args /\
  EVERY (\(name,ty,sz). sz = type_memory_bytes ce ty) fields /\
  LIST_REL (abi_decoder_coherent ce (env \\ nsid)
    (sf \\ nsid_to_string nsid)) (MAP SND args) tvs /\
  LIST_REL (abi_malformed_bounded_type_contract ce (env \\ nsid)
    (sf \\ nsid_to_string nsid)) (MAP SND args) tvs /\
  abi_decoder_header ce env (StructT nsid) (StructTV (ZIP (MAP FST args,tvs))) ==>
  abi_malformed_bounded_type_contract ce env sf (StructT nsid)
    (StructTV (ZIP (MAP FST args,tvs)))
Proof
  strip_tac >> simp_tac bool_ss [abi_malformed_bounded_type_contract_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all abi_malformed_struct_capacity >> strip_tac >>
  `abi_malformed_members_contract ce (env \\ nsid) (sf \\ nsid_to_string nsid)
    (MAP SND args) tvs` by
    (irule abi_malformed_bounded_members >> simp[]) >>
  `MAP (FST o SND) fields = MAP SND args` by
    (qpat_x_assum `MAP _ fields = args` (SUBST1_TAC o SYM) >>
     simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]) >>
  `LENGTH tvs = LENGTH args` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (irule type_memory_size_fields_zip >> simp[]) >>
  `EVERY (assignable_type (env \\ nsid)) (MAP SND args) /\
   type_memory_size_list tvs < dimword (:256) /\
   type_memory_size_list tvs <= outsz` by
    (fs[assignable_type_def, type_memory_size_def, abi_decoder_header_def, SF ETA_ss] >>
     gvs[EVERY_MAP]) >>
  `EVERY (\ty. ?av. has_type (vyper_to_abi_type (env \\ nsid) ty) av) (MAP SND args)` by
    (qpat_x_assum `has_type _ av` mp_tac >>
     simp[Once vyper_to_abi_type_def] >>
     Cases_on `av` >> simp[has_type_def] >> strip_tac >>
     drule abi_malformed_inhabited_members >> simp[]) >>
  `LENGTH args < dimword (:256)` by
    (qpat_x_assum `has_type _ av` mp_tac >> simp[Once vyper_to_abi_type_def] >>
     Cases_on `av` >> simp[has_type_def] >> strip_tac >>
     drule has_types_length >> simp[vyper_to_abi_types_MAP]) >>
  drule abi_decoder_struct_infos >> strip_tac >>
  fs[] >>
  simp_tac bool_ss [abi_malformed_constructor_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  irule frag_exec_pointwise >> gen_tac >>
  disch_then (strip_assume_tac o BETA_RULE) >> fs[] >>
  irule frag_exec_conseq >>
  drule_all abi_malformed_aggregate_fragment >>
  disch_then (irule_at Any) >> simp[] >>
  rpt strip_tac >> simp[abi_malformed_reflected_post_def] >>
  Cases_on `any_dynamic (vyper_to_abi_types (env \\ nsid) (MAP SND args))`
  >- (simp[Once vyper_to_abi_type_def, Once vyper_decode_valid_enc_def,
           vyper_to_abi_types_MAP, abi_decode_members_value] >>
      irule abiVyperAdmissibleTheory.struct_case >> simp[]) >>
  qspec_then `vyper_to_abi_types (env \\ nsid) (MAP SND args)` mp_tac
    abi_malformed_static_members_trim >>
  disch_then (qspecl_then
    [`TAKE (static_length (Tuple (vyper_to_abi_types (env \\ nsid) (MAP SND args)))) (DROP p xs)`,
     `DROP p xs`, `DROP p xs`,
     `static_length (Tuple (vyper_to_abi_types (env \\ nsid) (MAP SND args)))`] mp_tac) >>
  simp[static_length_Tuple_SUM, vyper_to_abi_types_MAP] >> strip_tac >>
  simp[Once vyper_to_abi_type_def, Once vyper_decode_valid_enc_def,
       vyper_to_abi_types_MAP, abi_decode_members_value] >>
  irule abiVyperAdmissibleTheory.struct_case >> simp[]
QED

Theorem abi_malformed_bounded_fixed_contract:
  abi_decoder_coherent ce env sf ty tv /\
  abi_malformed_bounded_type_contract ce env sf ty tv /\
  abi_decoder_header ce env (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) ==>
  abi_malformed_bounded_type_contract ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
Proof
  strip_tac >>
  Cases_on `n = 0`
  >- (gvs[] >> irule abi_malformed_zero_fixed_contract >>
      simp[abi_decoder_coherent_array_iff]) >>
  simp_tac bool_ss [abi_malformed_bounded_type_contract_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all abi_malformed_array_capacity >> simp[] >> strip_tac >>
  `abi_size_bound sf ty < dimword (:256)` by simp[] >>
  `abi_malformed_members_contract ce env sf (REPLICATE n ty) (REPLICATE n tv)` by
    (irule abi_malformed_bounded_members >> simp[LIST_REL_REPLICATE_same, EVERY_REPLICATE]) >>
  `type_memory_size_list (REPLICATE n tv) = n * type_memory_size tv` by
    (rpt (pop_assum kall_tac) >> Induct_on `n` >> simp[type_memory_size_def, MULT_CLAUSES]) >>
  `EVERY (assignable_type env) (REPLICATE n ty) /\
   type_memory_size_list (REPLICATE n tv) < dimword (:256) /\
   type_memory_size_list (REPLICATE n tv) <= outsz` by
    fs[assignable_type_def, type_memory_size_def, abi_decoder_header_def, EVERY_REPLICATE] >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `EVERY (\ty. ?av. has_type (vyper_to_abi_type env ty) av) (REPLICATE n ty)` by
    (qpat_x_assum `has_type _ av` mp_tac >>
     simp[Once vyper_to_abi_type_def] >>
     Cases_on `av` >> simp[has_type_def] >> strip_tac >> fs[] >>
     `has_types (vyper_to_abi_types env (REPLICATE n ty)) l` by
       fs[vyper_to_abi_types_MAP, map_replicate] >>
     drule abi_malformed_inhabited_members >> simp[] >> gvs[]) >>
  `n < dimword (:256)` by
    (qpat_x_assum `has_type _ av` mp_tac >> simp[Once vyper_to_abi_type_def] >>
     Cases_on `av` >> simp[has_type_def]) >>
  fs[abi_decoder_fixed_array_infos] >>
  simp_tac bool_ss [abi_malformed_constructor_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  irule frag_exec_pointwise >> gen_tac >>
  disch_then (strip_assume_tac o BETA_RULE) >> gvs[] >>
  irule frag_exec_conseq >>
  `LIST_REL (abi_decoder_coherent ce env sf) (REPLICATE n ty) (REPLICATE n tv) /\
   EVERY (assignable_type env) (REPLICATE n ty) /\
   EVERY (\ty. ?av. has_type (vyper_to_abi_type env ty) av) (REPLICATE n ty) /\
   type_memory_size_list (REPLICATE n tv) < dimword (:256) /\
   type_memory_size_list (REPLICATE n tv) <= outsz /\
   SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (REPLICATE n ty))) < dimword (:256)` by
     (simp[LIST_REL_REPLICATE_same, EVERY_REPLICATE, map_replicate, SUM_REPLICATE] >>
      metis_tac[]) >>
  drule_all abi_malformed_aggregate_fragment >>
  disch_then (irule_at Any) >> simp[] >>
  rpt strip_tac >> simp[abi_malformed_reflected_post_def] >>
  rewrite_tac[abi_decode_array_members, abi_decode_members_value] >>
  qpat_assum `vyper_decode_valid_enc_tuple _ _ _`
    (assume_tac o REWRITE_RULE [vyper_decode_valid_enc_tuple_REPLICATE]) >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)`
  >- (qpat_x_assum `vyper_decode_valid_enc_array _ _ _ _ _` mp_tac >>
      simp[] >> strip_tac >> simp[Once vyper_decode_valid_enc_def,
           GSYM vyper_decode_valid_enc_tuple_REPLICATE,
           abi_decode_array_members, abi_decode_members_value] >>
      irule abiVyperAdmissibleTheory.array >> simp[compatible_bound_def]) >>
  qspec_then `REPLICATE n (vyper_to_abi_type env ty)` mp_tac
    abi_malformed_static_members_trim >>
  disch_then (qspecl_then
    [`TAKE (n * static_length (vyper_to_abi_type env ty)) (DROP p xs)`,
     `DROP p xs`, `DROP p xs`, `n * static_length (vyper_to_abi_type env ty)`] mp_tac) >>
  simp[map_replicate, SUM_REPLICATE, any_dynamic_EXISTS] >> strip_tac >>
  qpat_assum `vyper_decode_valid_enc_tuple _ (TAKE _ _) _`
    (assume_tac o REWRITE_RULE [vyper_decode_valid_enc_tuple_REPLICATE]) >>
  simp[Once vyper_decode_valid_enc_def,
       GSYM vyper_decode_valid_enc_tuple_REPLICATE,
       abi_decode_array_members, abi_decode_members_value] >>
  conj_tac
  >- (qpat_x_assum `vyper_decode_valid_enc_array _ _ _ (TAKE _ _) _` mp_tac >> simp[]) >>
  irule abiVyperAdmissibleTheory.array >> simp[compatible_bound_def]
QED
