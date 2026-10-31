Theory abiStaticDynarrayLayout
Ancestors
  abiStaticAggregateProps valueEncoding vyperABI vyperTyping contractABI list
  abiStaticSparseProps abiStaticLayoutProps compileEnv rich_list valueEncodingTyping
  valueEncodingProps valueEncodingProofs vyperABIRoundtrip vyperTypeDefaults
  abiDecoderTypedContract arithmetic

(* Heterogeneous canonical bytes and recursive memory predicates. *)
Theorem static_typed_list_memory:
  !tys tvs vs avs off mem.
  LIST_REL (\ty tv.
    ~is_dynamic (vyper_to_abi_type tenv ty) /\
    (!v av. value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av ==>
      LENGTH (enc (vyper_to_abi_type tenv ty) av) = type_memory_size tv) /\
    (!v av off mem. value_has_type tv v /\
      vyper_to_abi tenv ty v = SOME av /\
      off + type_memory_size tv <= LENGTH mem /\
      mem_bytes_at off (type_memory_size tv) mem =
        enc (vyper_to_abi_type tenv ty) av ==>
      val_in_memory tv v off mem)) tys tvs /\
  values_have_types tvs vs /\ vyper_to_abi_list tenv tys vs = SOME avs /\
  off + type_memory_size_list tvs <= LENGTH mem /\
  mem_bytes_at off (type_memory_size_list tvs) mem =
    FLAT (MAP2 enc (vyper_to_abi_types tenv tys) avs) ==>
  tuple_in_memory vs tvs off mem
Proof
  Induct >> Cases_on `tvs` >> Cases_on `vs` >>
  simp[value_has_type_def, Once vyper_to_abi_def, type_memory_size_def,
       val_in_memory_def] >> rpt gen_tac >> rpt disch_tac >>
  gvs[AllCaseEqs()] >>
  `LIST_REL (\ty tv.
    ~is_dynamic (vyper_to_abi_type tenv ty) /\
    !v av. value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av ==>
      LENGTH (enc (vyper_to_abi_type tenv ty) av) = type_memory_size tv)
    tys t` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     match_mp_tac LIST_REL_mono >> simp[] >> metis_tac[]) >>
  drule_all static_typed_list_bss >> strip_tac >>
  `LENGTH (enc (vyper_to_abi_type tenv h'') av) = type_memory_size h` by
    metis_tac[] >>
  conj_tac
  >- (first_x_assum irule >> simp[] >>
      metis_tac[SRULE [] (Q.INST [`pre` |-> `[]`]
        abiStaticAggregatePropsTheory.mem_bytes_at_child_slice)]) >>
  first_x_assum irule >> simp[] >>
  metis_tac[SRULE [] (Q.INST [`post` |-> `[]`]
    abiStaticAggregatePropsTheory.mem_bytes_at_child_slice)]
QED

Theorem static_fields_memory_zip:
  !names tvs fs off mem.
  LENGTH names = LENGTH tvs /\ struct_has_type (ZIP(names,tvs)) fs /\
  tuple_in_memory (MAP SND fs) tvs off mem ==>
  fields_in_memory fs (ZIP(names,tvs)) off mem
Proof
  Induct >> Cases_on `tvs` >> Cases_on `fs` >>
  simp[value_has_type_def, val_in_memory_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h'` >> gvs[value_has_type_def, val_in_memory_def]
QED

(* Reverse canonical representation, not decoder execution. *)
Theorem static_sparse_memory_from_members[local]:
  !sp. (!k v. MEM (k,v) sp ==>
    val_in_memory tv v (off + k * type_memory_size tv) mem) ==>
    kvs_in_memory sp off tv mem
Proof
  Induct >> simp[val_in_memory_def] >> Cases_on `h` >>
  simp[val_in_memory_def] >> metis_tac[]
QED

Theorem static_sparse_lookup_type[local]:
  !sp k v. sparse_has_type tv n sp /\ ALOOKUP sp k = SOME v ==>
    value_has_type tv v
Proof
  Induct >> simp[value_has_type_def] >> Cases_on `h` >>
  simp[value_has_type_def] >> rpt strip_tac >>
  Cases_on `q = k` >> gvs[] >> metis_tac[]
QED

(* Absent sparse entries contribute the canonical ABI default chunk. *)
Theorem static_sparse_default_index[local]:
  !n sp avs k. vyper_to_abi_sparse tenv ty tv n sp = SOME avs /\
    k < n /\ ALOOKUP sp k = NONE ==>
    EL k avs = default_to_abi tv
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[Once vyper_to_abi_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac canonical_sparse_length >>
  Cases_on `k = n` >> fs[EL_APPEND_EQN] >>
  `k < n` by decide_tac >> gvs[] >> metis_tac[]
QED

Theorem static_children_memory[local]:
  LIST_REL (\ty tv. static_layout_compatible cenv tenv ty tv /\
    !v av off mem. value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av /\
      off + type_memory_size tv <= LENGTH mem /\
      mem_bytes_at off (type_memory_size tv) mem = enc (vyper_to_abi_type tenv ty) av ==>
      val_in_memory tv v off mem) tys tvs /\
  values_have_types tvs vs /\ vyper_to_abi_list tenv tys vs = SOME avs /\
  off + type_memory_size_list tvs <= LENGTH mem /\
  mem_bytes_at off (type_memory_size_list tvs) mem =
    enc (Tuple (vyper_to_abi_types tenv tys)) (ListV avs) ==>
  tuple_in_memory vs tvs off mem
Proof
  strip_tac >>
  `LIST_REL (\ty tv.
    ~is_dynamic (vyper_to_abi_type tenv ty) /\
    (!v av. value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av ==>
      LENGTH (enc (vyper_to_abi_type tenv ty) av) = type_memory_size tv) /\
    (!v av off mem. value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av /\
      off + type_memory_size tv <= LENGTH mem /\
      mem_bytes_at off (type_memory_size tv) mem = enc (vyper_to_abi_type tenv ty) av ==>
      val_in_memory tv v off mem)) tys tvs` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >> match_mp_tac LIST_REL_mono >>
     simp[] >> metis_tac[static_layout_compatible_properties, static_typed_encoding_length]) >>
  `LIST_REL (\ty tv.
    ~is_dynamic (vyper_to_abi_type tenv ty) /\
    !v av. value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av ==>
      LENGTH (enc (vyper_to_abi_type tenv ty) av) = type_memory_size tv) tys tvs` by
    (qpat_x_assum `LIST_REL (\ty tv. is_static _ /\ _) _ _` mp_tac >>
     match_mp_tac LIST_REL_mono >> simp[] >> metis_tac[]) >>
  drule_all static_typed_list_bss >> strip_tac >>
  gvs[enc_static_tuple, Excl "enc_def"] >>
  irule static_typed_list_memory >> simp[] >>
  qexistsl_tac [`avs`, `tenv`, `tys`] >> simp[]
QED

Theorem static_struct_zip_metadata[local]:
  !names tvs fs. LENGTH names = LENGTH tvs /\
    struct_has_type (ZIP(names,tvs)) fs ==>
    values_have_types tvs (MAP SND fs) /\
    type_memory_size_fields (ZIP(names,tvs)) = type_memory_size_list tvs
Proof
  Induct >> Cases_on `tvs` >> Cases_on `fs` >>
  simp[value_has_type_def, type_memory_size_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h'` >> gvs[value_has_type_def, type_memory_size_def] >> metis_tac[]
QED

Theorem static_canonical_memory_layout_bounded[local]:
  !cenv tenv ty tv. static_layout_compatible cenv tenv ty tv ==>
  !v av off mem.
    value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av /\
    off + type_memory_size tv <= LENGTH mem /\
    mem_bytes_at off (type_memory_size tv) mem =
      enc (vyper_to_abi_type tenv ty) av ==>
    val_in_memory tv v off mem
Proof
  ho_match_mp_tac static_layout_compatible_strongind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >- (irule abi_static_primitive_layout >>
      simp[] >> qexists_tac `av` >> gvs[Once vyper_to_abi_def] >>
      Cases_on `bt` >> gvs[type_memory_size_def, is_word_type_def] >>
      Cases_on `b` >> gvs[type_memory_size_def, is_word_type_def])
  >- (irule abi_compatible_flag_value_layout >> simp[] >> qexistsl_tac [`av`, `nsid`, `tenv`] >>
      gvs[type_memory_size_def])
  >- (Cases_on `v` >> gvs[value_has_type_def] >>
      rename1 `ArrayV arr` >> Cases_on `arr` >> gvs[value_has_type_def] >>
      rename1 `SArrayV sp` >>
      drule static_layout_compatible_properties >> strip_tac >>
      gvs[Once vyper_to_abi_def, AllCaseEqs(), Excl "enc_def"] >>
      `EVERY (\av. LENGTH (enc (vyper_to_abi_type tenv ty) av) =
        type_memory_size tv) avs` by
        (irule (cj 2 static_sparse_chunk_lengths) >>
         qexistsl_tac [`n`, `sp`, `tv`] >> simp[] >> conj_tac
         >- metis_tac[static_sparse_lookup_type] >>
         metis_tac[static_default_encoding_length, static_typed_encoding_length]) >>
      drule_all canonical_typed_sparse_index >> strip_tac >>
      gvs[enc_static_array, type_memory_size_def, val_in_memory_def, Excl "enc_def"] >>
      `!k v. k < LENGTH avs /\ value_has_type tv v /\
        vyper_to_abi tenv ty v = SOME (EL k avs) ==>
        val_in_memory tv v (off + k * type_memory_bytes cenv ty) mem` by
        (rpt strip_tac >>
         `k * type_memory_bytes cenv ty + type_memory_bytes cenv ty <=
           LENGTH avs * type_memory_bytes cenv ty` by
           (qspecl_then [`k + 1`, `LENGTH avs`, `type_memory_bytes cenv ty`]
             mp_tac arithmeticTheory.LESS_MONO_MULT >>
            pure_rewrite_tac[arithmeticTheory.RIGHT_ADD_DISTRIB,
              arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
         first_x_assum irule >> conj_tac >- gvs[] >>
         conj_tac >- (qexists_tac `EL k avs` >> simp[] >>
           `EVERY (\bs. LENGTH bs = type_memory_bytes cenv ty)
             (MAP (enc (vyper_to_abi_type tenv ty)) avs)` by simp[EVERY_MAP] >>
           drule static_mem_flat_chunk >> simp[EL_MAP] >>
           disch_then irule >> simp[]) >> simp[]) >>
      conj_tac
      >- (irule static_sparse_memory_from_members >> rpt strip_tac >>
          gvs[] >> first_x_assum irule >>
          metis_tac[static_sparse_lookup_type, sorted_sparse_ALOOKUP]) >>
      rpt strip_tac >> first_x_assum irule >> simp[] >>
      drule_all static_sparse_default_index >> strip_tac >>
      metis_tac[default_value_has_type_thm, cj 1 vyper_to_abi_default_value])
  >- (Cases_on `v` >> gvs[value_has_type_def] >>
      rename1 `ArrayV arr` >> Cases_on `arr` >> gvs[value_has_type_def] >>
      gvs[Once vyper_to_abi_def, AllCaseEqs(), Excl "enc_def"] >>
      simp[val_in_memory_def] >> irule static_children_memory >>
      gvs[type_memory_size_def, Excl "enc_def"] >>
      qexistsl_tac [`avs`, `cenv`, `tenv`, `tys`] >> simp[])
  >> Cases_on `v` >> gvs[value_has_type_def]
  >> `LENGTH (MAP FST args) = LENGTH tvs` by
       (imp_res_tac LIST_REL_LENGTH >> gvs[])
  >> simp[val_in_memory_def]
  >> irule static_fields_memory_zip >> simp[]
  >> drule_all static_struct_zip_metadata >> strip_tac
  >> gvs[AllCaseEqs(), type_memory_size_def, Excl "enc_def"]
  >> irule static_children_memory >> simp[]
  >> qexistsl_tac [`avs`, `cenv`, `tenv \\ nsid`, `MAP SND args`] >> simp[]
QED

(* Padded observations do not require the canonical bytes to be physically
   present: extending memory with zero bytes preserves every observed window. *)
Theorem static_canonical_memory_layout:
  !cenv tenv ty tv. static_layout_compatible cenv tenv ty tv ==>
  !v av off mem.
    value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av /\
    mem_bytes_at off (type_memory_size tv) mem =
      enc (vyper_to_abi_type tenv ty) av ==>
    val_in_memory tv v off mem
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `padded = mem ++ REPLICATE (off + type_memory_size tv) 0w` >>
  `off + type_memory_size tv <= LENGTH padded` by simp[Abbr `padded`] >>
  `mem_bytes_at off (type_memory_size tv) padded =
    enc (vyper_to_abi_type tenv ty) av` by
    simp[Abbr `padded`, mem_bytes_at_append_zero] >>
  `val_in_memory tv v off padded` by
    (drule static_canonical_memory_layout_bounded >>
     disch_then (qspecl_then [`v`, `av`, `off`, `padded`] mp_tac) >>
     asm_simp_tac bool_ss []) >>
  `val_wf tv v` by (drule_all (cj 1 value_has_type_val_wf) >> simp[]) >>
  irule val_in_memory_relocate >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`padded`, `type_memory_size tv`, `off`] >>
  simp[Abbr `padded`, mem_bytes_at_append_zero]
QED

(* Audit the entire export surface, including dependency-propagated tags. *)

(* Canonical static element payloads in a dynamic array's memory layout. *)
Theorem mem_bytes_at_append_parts:
  !off prefix suffix mem.
  mem_bytes_at off (LENGTH (prefix ++ suffix)) mem = prefix ++ suffix ==>
  mem_bytes_at off (LENGTH prefix) mem = prefix /\
  mem_bytes_at (off + LENGTH prefix) (LENGTH suffix) mem = suffix
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (qspecl_then [`off`, `[]`, `prefix`, `suffix`, `mem`]
        mp_tac abi_decoder_source_subwindow >> gvs[]) >>
  drule abi_decoder_source_prefix >> simp[]
QED

Theorem static_same_canonical_layout:
  !ce env ty tv. static_layout_compatible ce env ty tv ==>
  !vs avs. all_have_type tv vs /\ vyper_to_abi_same env ty vs = SOME avs ==>
  LENGTH avs = LENGTH vs /\
  LENGTH (FLAT (MAP (enc (vyper_to_abi_type env ty)) avs)) =
    LENGTH vs * type_memory_size tv /\
  !off mem.
    mem_bytes_at off (LENGTH vs * type_memory_size tv) mem =
      FLAT (MAP (enc (vyper_to_abi_type env ty)) avs) ==>
    elems_in_memory vs off tv mem
Proof
  rpt gen_tac >> strip_tac >> Induct_on `vs`
  >- simp[vyper_to_abi_def, value_has_type_def, val_in_memory_def] >>
  qx_gen_tac `v` >> rpt gen_tac >> strip_tac >>
  gvs[Once vyper_to_abi_def, value_has_type_def, AllCaseEqs(), Excl "enc_def"] >>
  rename1 `vyper_to_abi env ty v = SOME av` >>
  rename1 `vyper_to_abi_same env ty vs = SOME rest_avs` >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = type_memory_size tv` by
    (drule static_typed_encoding_length >>
     disch_then (qspecl_then [`v`, `av`] mp_tac) >> asm_simp_tac bool_ss []) >>
  simp[Excl "enc_def", MULT_CLAUSES] >> rpt gen_tac >> strip_tac >>
  `mem_bytes_at off
      (LENGTH (enc (vyper_to_abi_type env ty) av ++
        FLAT (MAP (enc (vyper_to_abi_type env ty)) rest_avs))) mem =
    enc (vyper_to_abi_type env ty) av ++
        FLAT (MAP (enc (vyper_to_abi_type env ty)) rest_avs)` by
    (asm_simp_tac arith_ss [LENGTH_APPEND]) >>
  drule mem_bytes_at_append_parts >> strip_tac >>
  qpat_assum `LENGTH (enc (vyper_to_abi_type env ty) av) = _` (fn head_th =>
    qpat_assum `LENGTH (FLAT (MAP (enc (vyper_to_abi_type env ty)) rest_avs)) = _`
      (fn tail_th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [head_th, tail_th]))) >>
  CONV_TAC (ONCE_REWRITE_CONV [val_in_memory_def]) >> conj_tac
  >- (drule static_canonical_memory_layout >>
      disch_then (qspecl_then [`v`, `av`, `off`, `mem`] mp_tac) >>
      asm_simp_tac bool_ss []) >>
  first_x_assum irule >> asm_simp_tac arith_ss []
QED

Theorem static_dynarray_canonical_layout:
  static_layout_compatible ce env ty tv /\ all_have_type tv vs /\
  vyper_to_abi_same env ty vs = SOME avs /\
  mem_word_at d mem = n2w (LENGTH vs) /\
  mem_bytes_at (d + 32) (LENGTH vs * type_memory_size tv) mem =
    FLAT (MAP (enc (vyper_to_abi_type env ty)) avs) ==>
  val_in_memory (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) d mem
Proof
  strip_tac >> simp[val_in_memory_def] >>
  drule_all static_same_canonical_layout >> simp[]
QED
