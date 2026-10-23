(* Static concatenation boundaries.  No decoder execution is asserted here. *)
Theory abiStaticAggregateProps
Ancestors
  abiStaticPrimitiveProps abiStaticSparseProps contractABI list rich_list
  abiStaticLayoutProps valueEncoding vyperABI vyperTyping

Theorem enc_tuple_static_flat:
  !ts vs hl tl hds tls.
    LENGTH ts = LENGTH vs /\ ~any_dynamic ts ==>
    enc_tuple hl tl ts vs hds tls =
      FLAT (REVERSE hds) ++ FLAT (MAP2 enc ts vs) ++ FLAT (REVERSE tls)
Proof
  Induct >> Cases_on `vs` >>
  simp[enc_def, is_dynamic_def, REV_REVERSE_LEM] >> rpt strip_tac >>
  gvs[enc_def, is_dynamic_def, REV_REVERSE_LEM, REVERSE_APPEND, FLAT_APPEND,
      APPEND_ASSOC]
QED

Theorem enc_static_tuple:
  LENGTH ts = LENGTH vs /\ ~any_dynamic ts ==>
  enc (Tuple ts) (ListV vs) = FLAT (MAP2 enc ts vs)
Proof
  simp[Once enc_def, enc_tuple_static_flat]
QED

Theorem MAP2_enc_replicate[local]:
  !vs. MAP2 enc (REPLICATE (LENGTH vs) t) vs = MAP (enc t) vs
Proof
  Induct >> simp[]
QED

Theorem any_dynamic_replicate[local]:
  !n. ~is_dynamic t ==> ~any_dynamic (REPLICATE n t)
Proof
  Induct >> simp[is_dynamic_def]
QED

Theorem enc_static_array:
  ~is_dynamic t ==>
  enc (Array (SOME n) t) (ListV vs) = FLAT (MAP (enc t) vs)
Proof
  strip_tac >> simp[Once enc_def, enc_tuple_static_flat,
    is_dynamic_def, any_dynamic_replicate, MAP2_enc_replicate]
QED

Theorem static_default_list_metadata[local]:
  !tys tvs.
    LIST_REL (\ty tv.
      ~is_dynamic (vyper_to_abi_type tenv ty) /\
      LENGTH (enc (vyper_to_abi_type tenv ty) (default_to_abi tv)) =
        type_memory_size tv) tys tvs ==>
    ~any_dynamic (vyper_to_abi_types tenv tys) /\
    LENGTH (vyper_to_abi_types tenv tys) = LENGTH (default_to_abi_list tvs) /\
    LENGTH (FLAT (MAP2 enc (vyper_to_abi_types tenv tys)
      (default_to_abi_list tvs))) = type_memory_size_list tvs
Proof
  Induct >> Cases_on `tvs` >>
  simp[default_to_abi_def, type_memory_size_def, is_dynamic_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem static_default_list_length:
  LIST_REL (\ty tv.
      ~is_dynamic (vyper_to_abi_type tenv ty) /\
      LENGTH (enc (vyper_to_abi_type tenv ty) (default_to_abi tv)) =
        type_memory_size tv) tys tvs ==>
  LENGTH (enc (Tuple (vyper_to_abi_types tenv tys))
      (ListV (default_to_abi_list tvs))) = type_memory_size_list tvs
Proof
  strip_tac >> drule static_default_list_metadata >> strip_tac >>
  drule_all enc_static_tuple >> disch_then SUBST1_TAC >> simp[]
QED

Theorem aggregate_dimindex[local,simp]:
  dimindex(:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem static_fields_zip[local]:
  !names tvs. LENGTH names = LENGTH tvs ==>
    default_to_abi_fields (ZIP (names,tvs)) = default_to_abi_list tvs /\
    type_memory_size_fields (ZIP (names,tvs)) = type_memory_size_list tvs
Proof
  Induct >> Cases_on `tvs` >> simp[default_to_abi_def, type_memory_size_def]
QED

Theorem static_default_encoding_length:
  !cenv tenv ty tv.
    static_layout_compatible cenv tenv ty tv ==>
    LENGTH (enc (vyper_to_abi_type tenv ty) (default_to_abi tv)) =
      type_memory_size tv
Proof
  ho_match_mp_tac static_layout_compatible_strongind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (Cases_on `bt` >>
      gvs[compileEnvTheory.is_word_type_def, default_to_abi_def,
          enc_def, enc_number_def, type_memory_size_def,
          byteTheory.LENGTH_word_to_bytes, static_layout_header_def] >>
      Cases_on `b` >>
      gvs[compileEnvTheory.is_word_type_def, default_to_abi_def,
          enc_def, enc_number_def, type_memory_size_def,
          byteTheory.LENGTH_word_to_bytes, LENGTH_TAKE_EQ])
  >- simp[default_to_abi_def, enc_def, enc_number_def,
          type_memory_size_def, byteTheory.LENGTH_word_to_bytes]
  >- (drule static_layout_compatible_properties >> strip_tac >>
      simp[default_to_abi_def, enc_static_array, LENGTH_FLAT,
           map_replicate, SUM_REPLICATE, type_memory_size_def])
  >- (pure_rewrite_tac[default_to_abi_def, type_memory_size_def,
                          vyper_to_abi_type_def] >>
      irule static_default_list_length >>
      qpat_x_assum `LIST_REL _ _ _` mp_tac >>
      match_mp_tac LIST_REL_mono >> simp[] >> rpt strip_tac >>
      drule static_layout_compatible_properties >> simp[])
  >> `LENGTH (MAP FST args) = LENGTH tvs` by
       (imp_res_tac LIST_REL_LENGTH >> gvs[])
  >> drule static_fields_zip >> strip_tac
  >> asm_rewrite_tac[vyper_to_abi_type_def, default_to_abi_def,
                     type_memory_size_def]
  >> simp[Excl "enc_def"]
  >> irule static_default_list_length
  >> qpat_x_assum `LIST_REL _ _ _` mp_tac
  >> match_mp_tac LIST_REL_mono >> simp[] >> rpt strip_tac
  >> drule static_layout_compatible_properties >> simp[]
QED

Theorem static_typed_list_bss:
  !tys tvs vs avs.
  LIST_REL (\ty tv.
    ~is_dynamic (vyper_to_abi_type tenv ty) /\
    !v av. value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av ==>
      LENGTH (enc (vyper_to_abi_type tenv ty) av) = type_memory_size tv)
    tys tvs /\ values_have_types tvs vs /\
  vyper_to_abi_list tenv tys vs = SOME avs ==>
  ~any_dynamic (vyper_to_abi_types tenv tys) /\
  LENGTH (vyper_to_abi_types tenv tys) = LENGTH avs /\
  LENGTH (FLAT (MAP2 enc (vyper_to_abi_types tenv tys) avs)) =
    type_memory_size_list tvs
Proof
  Induct >> Cases_on `tvs` >> Cases_on `vs` >>
  simp[value_has_type_def, Once vyper_to_abi_def, is_dynamic_def,
       type_memory_size_def] >> rpt gen_tac >> rpt disch_tac >>
  gvs[AllCaseEqs()] >>
  qpat_x_assum `!tvs vs avs. _` drule_all >> strip_tac >>
  simp[] >> metis_tac[]
QED

Theorem static_typed_tuple_length:
  LIST_REL (\ty tv.
    ~is_dynamic (vyper_to_abi_type tenv ty) /\
    !v av. value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av ==>
      LENGTH (enc (vyper_to_abi_type tenv ty) av) = type_memory_size tv)
    tys tvs /\ values_have_types tvs vs /\
  vyper_to_abi_list tenv tys vs = SOME avs ==>
  LENGTH (enc (Tuple (vyper_to_abi_types tenv tys)) (ListV avs)) =
    type_memory_size_list tvs
Proof
  strip_tac >> drule_all static_typed_list_bss >> strip_tac >>
  drule_all enc_static_tuple >> disch_then SUBST1_TAC >> simp[]
QED

Theorem sparse_has_type_lookup[local]:
  !sparse k v. sparse_has_type tv n sparse /\ ALOOKUP sparse k = SOME v ==>
    value_has_type tv v
Proof
  Induct >> simp[value_has_type_def] >>
  Cases_on `h` >> simp[value_has_type_def] >> rpt strip_tac >>
  Cases_on `q = k` >> gvs[] >> metis_tac[]
QED

Theorem static_sparse_chunk_lengths:
  !n avs.
  (!v av. value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av ==>
    LENGTH (enc (vyper_to_abi_type tenv ty) av) = sz) /\
  LENGTH (enc (vyper_to_abi_type tenv ty) (default_to_abi tv)) = sz /\
  (!k v. ALOOKUP sparse k = SOME v ==> value_has_type tv v) /\
  vyper_to_abi_sparse tenv ty tv n sparse = SOME avs ==>
  LENGTH avs = n /\ EVERY (\av. LENGTH (enc (vyper_to_abi_type tenv ty) av) = sz) avs
Proof
  Induct >> simp[Once vyper_to_abi_def] >> rpt gen_tac >> rpt disch_tac >>
  gvs[AllCaseEqs()] >> qpat_x_assum `(_ /\ _) ==> _` drule_all >> strip_tac >>
  simp[EVERY_APPEND] >> metis_tac[]
QED

Theorem static_primitive_encoding_length[local]:
  is_word_type (BaseT bt) /\ value_has_type (BaseTV bt) v /\
  vyper_to_abi_base bt v = SOME av ==>
  LENGTH (enc (vyper_base_to_abi_type bt) av) = 32
Proof
  Cases_on `bt` >> Cases_on `v` >>
  simp[compileEnvTheory.is_word_type_def, vyper_to_abi_base_def] >>
  rpt strip_tac >> gvs[value_has_type_def, enc_def, enc_number_def,
    byteTheory.LENGTH_word_to_bytes, LENGTH_TAKE_EQ] >>
  Cases_on `b` >> gvs[compileEnvTheory.is_word_type_def,
    value_has_type_def, enc_def, enc_number_def, LENGTH_TAKE_EQ]
QED

Theorem static_fixed_value_shape[local]:
  value_has_type (ArrayTV tv (Fixed n)) v ==>
  ?sp. v = ArrayV (SArrayV sp) /\ sparse_has_type tv n sp /\
       SORTED $< (MAP FST sp)
Proof
  Cases_on `v` >> simp[value_has_type_def] >>
  rename1 `value_has_type _ (ArrayV arr)` >>
  Cases_on `arr` >> simp[value_has_type_def]
QED

Theorem static_tuple_value_shape[local]:
  value_has_type (TupleTV tvs) v ==>
  ?vs. v = ArrayV (TupleV vs) /\ values_have_types tvs vs
Proof
  Cases_on `v` >> simp[value_has_type_def] >>
  rename1 `value_has_type _ (ArrayV arr)` >>
  Cases_on `arr` >> simp[value_has_type_def]
QED

Theorem static_struct_value_shape[local]:
  value_has_type (StructTV fts) v ==>
  ?fs. v = StructV fs /\ struct_has_type fts fs
Proof
  Cases_on `v` >> simp[value_has_type_def] >>
  rename1 `value_has_type _ (ArrayV arr)` >>
  Cases_on `arr` >> simp[value_has_type_def]
QED

Theorem static_uniform_flat_length:
  !avs. EVERY (\av. LENGTH (enc t av) = sz) avs ==>
    LENGTH (FLAT (MAP (enc t) avs)) = LENGTH avs * sz
Proof
  Induct >> simp[arithmeticTheory.MULT_CLAUSES] >> rpt strip_tac >> gvs[]
QED

Theorem static_struct_values_types[local]:
  !names tvs fs. LENGTH names = LENGTH tvs /\
    struct_has_type (ZIP (names,tvs)) fs ==>
    values_have_types tvs (MAP SND fs)
Proof
  Induct >> Cases_on `tvs` >> Cases_on `fs` >>
  simp[value_has_type_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h'` >>
  gvs[value_has_type_def]
QED

Theorem static_typed_encoding_length:
  !cenv tenv ty tv.
  static_layout_compatible cenv tenv ty tv ==>
  !v av. value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av ==>
    LENGTH (enc (vyper_to_abi_type tenv ty) av) = type_memory_size tv
Proof
  ho_match_mp_tac static_layout_compatible_strongind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >- (`LENGTH (enc (vyper_base_to_abi_type bt) av) = 32` by
        (gvs[Once vyper_to_abi_def] >> irule static_primitive_encoding_length >>
         conj_tac >- simp[] >> qexists_tac `v` >> simp[]) >>
      Cases_on `bt` >> gvs[type_memory_size_def, compileEnvTheory.is_word_type_def] >>
      Cases_on `b` >> gvs[type_memory_size_def, compileEnvTheory.is_word_type_def])
  >- (Cases_on `v` >> gvs[value_has_type_def, enc_def, enc_number_def,
                          type_memory_size_def, byteTheory.LENGTH_word_to_bytes])
  >- (drule static_fixed_value_shape >> strip_tac >> gvs[] >>
      drule static_layout_compatible_properties >> strip_tac >>
      gvs[Once vyper_to_abi_def, AllCaseEqs(), Excl "enc_def"] >>
      `EVERY (\av. LENGTH (enc (vyper_to_abi_type tenv ty) av) =
                    type_memory_size tv) avs` by
        (irule (cj 2 static_sparse_chunk_lengths) >>
         qexistsl_tac [`n`, `sp`, `tv`] >>
         simp[] >> conj_tac
         >- metis_tac[sparse_has_type_lookup] >>
         metis_tac[static_default_encoding_length]) >>
      drule canonical_sparse_length >> strip_tac >>
      drule static_uniform_flat_length >> strip_tac >>
      drule enc_static_array >> strip_tac >>
      gvs[Excl "enc_def", type_memory_size_def])
  >- (drule static_tuple_value_shape >> strip_tac >> gvs[] >>
      gvs[Once vyper_to_abi_def, AllCaseEqs(), Excl "enc_def"] >>
      pure_rewrite_tac[type_memory_size_def, vyper_to_abi_type_def] >>
      irule static_typed_tuple_length >>
      conj_tac >- (qexists_tac `vs` >> simp[]) >>
      qpat_x_assum `LIST_REL _ _ _` mp_tac >>
      match_mp_tac LIST_REL_mono >> simp[] >> rpt strip_tac >>
      drule static_layout_compatible_properties >> strip_tac >> gvs[] >>
      metis_tac[])
  >> drule static_struct_value_shape >> strip_tac >> gvs[]
  >> `LENGTH (MAP FST args) = LENGTH tvs` by
       (imp_res_tac LIST_REL_LENGTH >> gvs[])
  >> drule_all static_struct_values_types >> strip_tac
  >> drule static_fields_zip >> strip_tac
  >> gvs[Once vyper_to_abi_def, AllCaseEqs(), Excl "enc_def"]
  >> asm_rewrite_tac[vyper_to_abi_type_def, type_memory_size_def]
  >> simp[Excl "enc_def"]
  >> irule static_typed_tuple_length
  >> conj_tac >- (qexists_tac `MAP SND fs` >> simp[])
  >> qpat_x_assum `LIST_REL _ _ _` mp_tac
  >> match_mp_tac LIST_REL_mono >> simp[] >> rpt strip_tac
  >> drule static_layout_compatible_properties >> strip_tac >> gvs[]
  >> metis_tac[]
QED

Theorem static_mem_subslice:
  mem_bytes_at off (LENGTH bs) mem = bs /\
  off + LENGTH bs <= LENGTH mem /\ k + n <= LENGTH bs ==>
  mem_bytes_at (off + k) n mem = TAKE n (DROP k bs)
Proof
  rpt strip_tac >>
  `off + k + n <= LENGTH mem` by decide_tac >>
  gvs[mem_bytes_at_bounded] >>
  qpat_x_assum `TAKE _ _ = _` (SUBST1_TAC o SYM) >>
  simp[DROP_TAKE, TAKE_TAKE, DROP_DROP, arithmeticTheory.MIN_DEF]
QED

Theorem static_flat_chunk_slice:
  !bss k.
  EVERY (\bs:byte list. LENGTH bs = sz) bss /\ k < LENGTH bss ==>
  TAKE sz (DROP (k * sz) (FLAT bss)) = EL k bss
Proof
  Induct >> simp[] >> Cases_on `k` >> simp[] >> rpt strip_tac >>
  gvs[DROP_APPEND, TAKE_APPEND, arithmeticTheory.MULT_CLAUSES,
      DROP_LENGTH_TOO_LONG] >>
  `LENGTH h - (LENGTH h + n * LENGTH h) = 0` by decide_tac >> gvs[]
QED

Theorem static_flat_bss_length:
  !bss:byte list list. EVERY (\bs. LENGTH bs = sz) bss ==>
  LENGTH (FLAT bss) = LENGTH bss * sz
Proof
  Induct >> simp[arithmeticTheory.MULT_CLAUSES]
QED

Theorem static_mem_flat_chunk:
  EVERY (\bs:byte list. LENGTH bs = sz) bss /\ k < LENGTH bss /\
  mem_bytes_at off (LENGTH bss * sz) mem = FLAT bss /\
  off + LENGTH bss * sz <= LENGTH mem ==>
  mem_bytes_at (off + k * sz) sz mem = EL k bss
Proof
  rpt strip_tac >> drule static_flat_bss_length >> strip_tac >>
  `k * sz + sz <= LENGTH bss * sz` by
    (qspecl_then [`k + 1`, `LENGTH bss`, `sz`] mp_tac
       arithmeticTheory.LESS_MONO_MULT >>
     pure_rewrite_tac[arithmeticTheory.RIGHT_ADD_DISTRIB,
                      arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  `mem_bytes_at (off + k * sz) sz mem =
    TAKE sz (DROP (k * sz) (FLAT bss))` by
    (irule static_mem_subslice >> gvs[arithmeticTheory.MULT_COMM] >> decide_tac) >>
  simp[] >> irule static_flat_chunk_slice >> simp[]
QED

(* Check every exported theorem, including cached dependencies' propagated tags. *)
val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_STATIC_AGGREGATE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI static aggregate not kernel closed: " ^ n)
  end) (DB.thms "abiStaticAggregateProps");
