Theory abiDecoderFixedInputs
Ancestors
  abiDecoderMembers abiDecoderStruct abiDecoderCoherence abiDecoderTypedContract compileEnv
  valueEncoding vyperABI vyperValue vyperTyping vyperTypeABI vyperTypeDefaults contractABI words
  list rich_list abiDecoderPreObservations abiDecoderContract abiDecoderReentry
  abiCanonicalHeadSize venomState

(* Recover a dense homogeneous member view from fixed-array conversion. *)
Theorem abi_decoder_fixed_array_values:
  abi_decoder_coherent ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) /\
  abi_decoder_metadata ce env (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) di av v ==>
  ?avs vs. av = ListV avs /\
    v = ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs)) /\
    LENGTH avs = n /\ LENGTH vs = n /\
    abi_decoder_members ce env sf (REPLICATE n ty) (REPLICATE n tv) avs vs
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  drule abi_decoder_coherent_header >> strip_tac >>
  `evaluate_type env ty = SOME tv` by fs[abi_decoder_header_def] >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  `?avs. av = ListV avs` by
    (Cases_on `av` >> fs[Once abi_to_vyper_def, Excl "enc_def"]) >>
  qpat_x_assum `av = ListV avs` SUBST_ALL_TAC >>
  `LENGTH avs = n /\ has_types (REPLICATE n (vyper_to_abi_type env ty)) avs` by
    (fs[Once vyper_to_abi_type_def, Once has_type_def, Excl "enc_def"] >> gvs[Excl "enc_def"]) >>
  Cases_on `abi_to_vyper_list env (REPLICATE n ty) avs` >- fs[Excl "enc_def"] >>
  rename1 `abi_to_vyper_list env (REPLICATE n ty) avs = SOME vs` >>
  `v = ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))` by
    (fs[make_array_value_def, Excl "enc_def"] >> gvs[Excl "enc_def"]) >>
  `LIST_REL (abi_decoder_coherent ce env sf) (REPLICATE n ty) (REPLICATE n tv)`
    by simp[LIST_REL_REPLICATE_same] >>
  `LIST_REL value_has_type (REPLICATE n tv) vs` by
    (mp_tac (Q.SPECL [`env`, `REPLICATE n ty`, `avs`, `vs`, `REPLICATE n tv`]
      (cj 2 abi_to_vyper_well_typed)) >>
     asm_simp_tac (srw_ss()) [LIST_REL_REPLICATE_same, values_have_types_LIST_REL]) >>
  `abi_decoder_members ce env sf (REPLICATE n ty) (REPLICATE n tv) avs vs` by
    (irule abi_decoder_members_intro >> simp[map_replicate]) >>
  drule abi_decoder_members_lengths >> strip_tac >>
  qexistsl_tac [`avs`, `vs`] >> gvs[Excl "enc_def"]
QED

(* Canonical fixed-array bytes are the repeated-type tuple encoding. *)
Theorem abi_decoder_fixed_array_inputs:
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) di av v
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) ==>
  ?avs vs. av = ListV avs /\
    v = ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs)) /\ LENGTH vs = n /\
    abi_decoder_members ce env sf (REPLICATE n ty) (REPLICATE n tv) avs vs /\
    type_memory_bytes ce (ArrayT ty (Fixed n)) = SUM (MAP (type_memory_bytes ce) (REPLICATE n ty)) /\
    abi_decoder_ranges opc hi src dst sb
      (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (REPLICATE n ty))) (ListV avs)))
      d (SUM (MAP (type_memory_bytes ce) (REPLICATE n ty))) b cap initial /\
    mem_bytes_at sb
      (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (REPLICATE n ty))) (ListV avs)))
      (abi_decode_source opc initial) =
        enc (Tuple (MAP (vyper_to_abi_type env) (REPLICATE n ty))) (ListV avs) /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi
Proof
  strip_tac >> drule abi_decoder_pre_observations >> strip_tac >>
  drule_all abi_decoder_fixed_array_values >> strip_tac >>
  `type_memory_bytes ce (ArrayT ty (Fixed n)) = SUM (MAP (type_memory_bytes ce) (REPLICATE n ty))`
    by simp[Once type_memory_bytes_def, map_replicate, SUM_REPLICATE] >>
  gvs[Once vyper_to_abi_type_def, canonical_array_tuple, map_replicate, Excl "enc_def"] >>
  metis_tac[]
QED
