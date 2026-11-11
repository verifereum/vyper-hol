(* Tuple, struct and fixed-array adapters for successful owned decoding. *)
Theory abiValidAllocatedAggregate
Ancestors
  abiValidAllocatedComplex abiValidAllocatedMemberFold abiValidAllocatedMembers
  abiValidAllocatedContract abiDecoderMemberInfos abiDecoderCoherence
  abiMalformedRecursiveInterface abiValidMembers abiValidAggregateHeads
  abiDecoderContract abiEncoder vyperABI contractABI compileEnv valueEncoding
  vyperValue abiDecodeRanges abiDecoderMembers words list rich_list arithmetic
  abiDecoderStruct valueEncodingTyping valueEncodingProofs finite_map
  abiDecoderFixedMemory vyperABIValid exprSimAggregateEncoding

Theorem abi_valid_allocated_tuple:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL (abi_valid_allocated_type_contract ce env sf) tys tvs ==>
  abi_valid_allocated_type_contract ce env sf (TupleT tys) (TupleTV tvs)
Proof
  strip_tac >> drule_all abi_valid_allocated_members_fold >> strip_tac >>
  rewrite_tac[abi_valid_allocated_type_contract_def] >> rpt gen_tac >> strip_tac >>
  qhdtm_assum `abi_valid_allocated_entry`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  drule abi_decoder_coherent_header >> strip_tac >>
  `type_memory_bytes ce (TupleT tys) = type_memory_size_list tvs` by
    fs[abi_decoder_header_def, type_memory_size_def] >>
  `vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys)
     (DROP p xs) (DROP p xs)` by
    (fs[vyper_to_abi_type_def, vyper_to_abi_types_MAP] >>
     gvs[Once vyper_decode_valid_enc_def]) >>
  `dec (vyper_to_abi_type env (TupleT tys)) (DROP p xs) =
    ListV (abi_decode_members (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP p xs))` by
    simp[vyper_to_abi_type_def, vyper_to_abi_types_MAP,
         Once dec_def, abi_decode_members_value] >>
  `?vs. v = ArrayV (TupleV vs) /\ abi_to_vyper_list env tys
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP p xs)) = SOME vs` by
    (fs[Once abi_to_vyper_def, AllCaseEqs()] >> metis_tac[]) >>
  gvs[] >>
  `compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) tys)
      (abi_decoder_member_infos sf ce tys)) st = ((),en)` by
    fs[abi_decoder_tuple_infos] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ (type_to_abi_dec_info _ _ _) _ = _` kall_tac >>
  `?t. abi_valid_allocated_members_post tvs vs ctx func cenv cx es st en ceiling dstid
      d (type_memory_size_list tvs) s t` by
    (irule abi_valid_allocated_complex_members >>
     simp[] >>
     qhdtm_assum `abi_malformed_entry` (irule_at Any) >>
     qhdtm_assum `abi_to_vyper_list` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  qexists_tac `t` >>
  fs[abi_valid_allocated_post_def, abi_valid_allocated_members_post_def,
     val_in_memory_def]
QED

Theorem abi_valid_allocated_struct:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
  MAP (\(name,ty,sz). (name,ty)) fields = args /\
  LIST_REL (abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid))
    (MAP SND args) tvs /\
  LIST_REL (abi_valid_allocated_type_contract ce (env \\ nsid) (sf \\ nsid_to_string nsid))
    (MAP SND args) tvs ==>
  abi_valid_allocated_type_contract ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
  strip_tac >> drule_all abi_valid_allocated_members_fold >> strip_tac >>
  `LENGTH tvs = LENGTH args` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by simp[] >>
  `MAP (FST o SND) fields = MAP SND args` by
    (qpat_x_assum `MAP _ fields = args` (SUBST1_TAC o SYM) >>
     simp[MAP_MAP_o, combinTheory.o_DEF] >>
     irule MAP_CONG >> simp[pairTheory.FORALL_PROD]) >>
  rewrite_tac[abi_valid_allocated_type_contract_def] >> rpt gen_tac >> strip_tac >>
  qhdtm_assum `abi_valid_allocated_entry`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  drule abi_decoder_coherent_header >> strip_tac >>
  `type_memory_bytes ce (StructT nsid) = type_memory_size_list tvs` by
    (`type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
       (irule type_memory_size_fields_zip >> simp[]) >>
     fs[abi_decoder_header_def, type_memory_size_def]) >>
  `vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))
     (DROP p xs) (DROP p xs)` by
    (fs[vyper_to_abi_type_def, vyper_to_abi_types_MAP] >>
     gvs[Once vyper_decode_valid_enc_def]) >>
  `dec (vyper_to_abi_type env (StructT nsid)) (DROP p xs) = ListV
    (abi_decode_members (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) (DROP p xs) (DROP p xs))` by
    simp[vyper_to_abi_type_def, vyper_to_abi_types_MAP, Once dec_def, abi_decode_members_value] >>
  qpat_assum `dec (vyper_to_abi_type env (StructT nsid)) _ = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  drule abi_decoder_struct_values >> strip_tac >>
  qpat_x_assum `v = StructV _` SUBST_ALL_TAC >>
  drule_all abi_decoder_struct_conversion >> strip_tac >>
  `compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) (MAP SND args))
      (abi_decoder_member_infos (sf \\ nsid_to_string nsid) ce (MAP SND args))) st = ((),en)` by
    (drule abi_decoder_struct_infos >> disch_then (qspec_then `ce` mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  `?t. abi_valid_allocated_members_post tvs (MAP SND fields') ctx func cenv cx es st en ceiling dstid
      d (type_memory_size_list tvs) s t` by
    (irule abi_valid_allocated_complex_members >> simp[] >> metis_tac[]) >>
  qexists_tac `t` >>
  fs[abi_valid_allocated_post_def, abi_valid_allocated_members_post_def,
     val_in_memory_def, fields_in_memory_tuple, MAP_ZIP]
QED

Theorem abi_valid_allocated_fixed_array:
  abi_decoder_coherent ce env sf ty tv /\
  abi_valid_allocated_type_contract ce env sf ty tv ==>
  abi_valid_allocated_type_contract ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
Proof
  strip_tac >>
  `LIST_REL (abi_decoder_coherent ce env sf) (REPLICATE n ty) (REPLICATE n tv) /\
   LIST_REL (abi_valid_allocated_type_contract ce env sf) (REPLICATE n ty) (REPLICATE n tv)` by
    simp[LIST_REL_REPLICATE_same] >>
  drule_all abi_valid_allocated_members_fold >> strip_tac >>
  rewrite_tac[abi_valid_allocated_type_contract_def] >> rpt gen_tac >> strip_tac >>
  qhdtm_assum `abi_valid_allocated_entry`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  `evaluate_type env ty = SOME tv` by
    (rev_drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  `type_memory_bytes ce (ArrayT ty (Fixed n)) = type_memory_size_list (REPLICATE n tv)` by
    (drule_at Any abi_decoder_coherent_header >>
     simp[abi_decoder_header_def, type_memory_size_def, type_memory_size_list_replicate]) >>
  `vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) (REPLICATE n ty))
     (DROP p xs) (DROP p xs)` by
    (fs[vyper_to_abi_type_def, Once vyper_decode_valid_enc_def] >>
     simp[map_replicate, vyper_decode_valid_enc_tuple_REPLICATE]) >>
  `dec (vyper_to_abi_type env (ArrayT ty (Fixed n))) (DROP p xs) = ListV
    (abi_decode_members (MAP (vyper_to_abi_type env) (REPLICATE n ty)) (DROP p xs) (DROP p xs))` by
    simp[vyper_to_abi_type_def, Once dec_def, abi_decode_array_members,
      map_replicate, abi_decode_members_value] >>
  qpat_assum `dec (vyper_to_abi_type env (ArrayT ty (Fixed n))) _ = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `LENGTH (abi_decode_members (MAP (vyper_to_abi_type env) (REPLICATE n ty))
     (DROP p xs) (DROP p xs)) = n` by
    (drule abi_valid_members_view >> strip_tac >>
     metis_tac[has_types_length, LENGTH_MAP, LENGTH_REPLICATE]) >>
  `?vs. abi_to_vyper_list env (REPLICATE n ty)
     (abi_decode_members (MAP (vyper_to_abi_type env) (REPLICATE n ty)) (DROP p xs) (DROP p xs)) = SOME vs /\
     v = ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))` by
    (fs[Once abi_to_vyper_def, make_array_value_def, AllCaseEqs()] >> metis_tac[]) >>
  `LENGTH vs = n` by metis_tac[abi_to_vyper_list_lengths, LENGTH_REPLICATE] >>
  `compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecComplex (is_abi_dynamic ce.ce_struct_fields ty)
      (abi_decoder_member_infos sf ce (REPLICATE n ty))) st = ((),en)` by
    fs[abi_decoder_fixed_array_infos] >>
  `?t. abi_valid_allocated_members_post (REPLICATE n tv) vs ctx func cenv cx es st en ceiling dstid
      d (type_memory_size_list (REPLICATE n tv)) s t` by
    (irule abi_valid_allocated_complex_members >> simp[] >> metis_tac[]) >>
  `val_in_memory (ArrayTV tv (Fixed n)) v d t.vs_memory` by
    (fs[abi_valid_allocated_members_post_def] >>
     irule abi_decoder_fixed_array_memory >> simp[]) >>
  qexists_tac `t` >> fs[abi_valid_allocated_post_def, abi_valid_allocated_members_post_def]
QED
