Theory exprSimAbiDecodeFixedArrayOwned
Ancestors
  exprSimAbiDecodeConstructorOutcome exprSimAbiDecodeArrayMembers
  exprSimAbiDecodeArrayBulk exprSimAbiDecodeComplexOutcome
  exprSimAbiDecodeMemberExecute vyperTypeABI
  exprSimAbiDecodeTupleAssembly abiDecoderFixedMemory
  exprSimAbiDecodeTupleOutcome exprSimAbiDecodeWidthBoundary
  abiDecoderCoherence valueEncoding exprLowering vyperTypeSystem
  exprSimAbiDecodeOwnedContext exprSimAbiDecodeOwnedRows
  exprSimAbiDecodeSiteProvenance abiDecoderComplexGuard abiDecoderFiniteControl
  abiDecoderSiteEffect abiEncoder compileEnv emitHelper exprLoweringProps
  abiValidAggregateHeads abiValidMembers vyperABIValid vyperABI contractABI
  vyperValue words list rich_list arithmetic

Theorem abi_decode_fixed_array_sparse_length_probe:
  abi_decode_source_accepts FEMPTY (ArrayT (BaseT BoolT) (Fixed 1))
    (REPLICATE 32 (0w:byte))
    (ArrayV (make_array_value (BaseTV BoolT) (Fixed 1) []))
Proof
  EVAL_TAC >> simp[dimword_def, wordsTheory.word_0_n2w] >> EVAL_TAC
QED

Theorem abi_decode_fixed_array_members_source:
  evaluate_type env ty = SOME tv /\
  n * abi_member_head_size (vyper_to_abi_type env ty) <= LENGTH bs /\
  n < dimword (:256) ==>
  (abi_decode_source_accepts env (ArrayT ty (Fixed n)) bs v <=>
   ?vs. LENGTH vs = n /\
   (!k. k < n ==> abi_decode_source_accepts env ty
     (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
       (DROP (k * abi_member_head_size (vyper_to_abi_type env ty)) bs)) (EL k vs)) /\
   v = ArrayV (make_array_value tv (Fixed n) vs))
Proof
  strip_tac >>
  `!vs. (vyper_decode_valid_enc_tuple (REPLICATE n (vyper_to_abi_type env ty)) bs bs /\
     abi_to_vyper_list env (REPLICATE n ty)
       (abi_decode_members (REPLICATE n (vyper_to_abi_type env ty)) bs bs) = SOME vs) <=>
    LENGTH vs = n /\ (!k. k < n ==> abi_decode_source_accepts env ty
      (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
        (DROP (k * abi_member_head_size (vyper_to_abi_type env ty)) bs)) (EL k vs))` by
    (gen_tac >> mp_tac (Q.SPECL [`n`, `env`, `ty`, `bs`, `0`, `vs`]
      abi_array_members_source) >> simp[]) >>
  pop_assum mp_tac >>
  simp_tac std_ss [abi_decode_source_accepts_def, vyper_to_abi_type_def,
    Once vyper_decode_valid_enc_def, Once dec_def, LET_THM,
    abi_decode_array_members, abi_decode_members_value,
    abi_to_vyper_def, abi_decode_members_length, LENGTH_REPLICATE,
    REVERSE_DEF, APPEND, compatible_bound_def,
    GSYM vyper_decode_valid_enc_tuple_REPLICATE] >>
  asm_simp_tac (srw_ss()) [DROP_0, make_array_value_def, AllCaseEqs(),
    Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  metis_tac[]
QED

Theorem abi_decode_fixed_array_source_intro:
  evaluate_type env ty = SOME tv /\
  n * abi_member_head_size (vyper_to_abi_type env ty) <= LENGTH bs /\
  n < dimword (:256) /\ LENGTH vs = n /\
  (!k. k < n ==> abi_decode_source_accepts env ty
    (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
      (DROP (k * abi_member_head_size (vyper_to_abi_type env ty)) bs)) (EL k vs)) ==>
  abi_decode_source_accepts env (ArrayT ty (Fixed n)) bs
    (ArrayV (make_array_value tv (Fixed n) vs))
Proof
  strip_tac >> drule_all abi_decode_fixed_array_members_source >> metis_tac[]
QED

Theorem abi_decode_fixed_array_member_reject:
  evaluate_type env ty = SOME tv /\
  n * abi_member_head_size (vyper_to_abi_type env ty) <= LENGTH bs /\
  n < dimword (:256) /\ k < n /\
  ~(?v. abi_decode_source_accepts env ty
    (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
      (DROP (k * abi_member_head_size (vyper_to_abi_type env ty)) bs)) v) ==>
  ~(?v. abi_decode_source_accepts env (ArrayT ty (Fixed n)) bs v)
Proof
  strip_tac >> drule_all abi_decode_fixed_array_members_source >> metis_tac[]
QED

Theorem abi_decode_fixed_rows_source:
  abi_tuple_rows_schema ce env (REPLICATE n (ei,ty,tv,asz,msz)) /\
  evaluate_type env ty = SOME tv /\
  asz = abi_member_head_size (vyper_to_abi_type env ty) /\
  n * asz <= LENGTH bs /\ n < dimword (:256) ==>
  (abi_decode_source_accepts env (ArrayT ty (Fixed n)) bs v <=>
   ?vs. abi_tuple_rows_accept env bs 0 (REPLICATE n (ei,ty,tv,asz,msz)) vs /\
     v = ArrayV (make_array_value tv (Fixed n) vs))
Proof
  strip_tac >>
  drule abi_tuple_rows_accept_source >>
  disch_then (qspecl_then [`bs`, `0`] mp_tac) >>
  simp[map_replicate, SUM_REPLICATE, abi_tuple_row_abi_width_def] >>
  strip_tac >>
  simp_tac std_ss [abi_decode_source_accepts_def, vyper_to_abi_type_def,
    Once vyper_decode_valid_enc_def, Once dec_def, LET_THM,
    abi_decode_array_members, abi_decode_members_value,
    abi_to_vyper_def, abi_decode_members_length, LENGTH_REPLICATE,
    REVERSE_DEF, APPEND, compatible_bound_def,
    GSYM vyper_decode_valid_enc_tuple_REPLICATE] >>
  asm_simp_tac (srw_ss()) [DROP_0, AllCaseEqs(), Excl "dec_def",
    Excl "vyper_decode_valid_enc_def"] >> metis_tac[]
QED

Theorem abi_decode_fixed_rows_memory:
  abi_tuple_rows_schema ce env (REPLICATE n (ei,ty,tv,asz,msz)) /\
  abi_tuple_rows_values env bs 0 0 d (REPLICATE n (ei,ty,tv,asz,msz)) vs s ==>
  val_in_memory (ArrayTV tv (Fixed n))
    (ArrayV (make_array_value tv (Fixed n) vs)) d s.vs_memory
Proof
  strip_tac >> drule_all abi_tuple_rows_values_memory >>
  simp[map_replicate] >> strip_tac >>
  simp_tac bool_ss [make_array_value_def] >>
  irule abi_decoder_fixed_array_memory >>
  drule abi_tuple_rows_values_length >> simp[]
QED

Theorem abi_decode_fixed_source_view_accept:
  abi_decode_source_accepts env (ArrayT ty (Fixed n))
    (abi_decode_source_view (vyper_to_abi_type env (ArrayT ty (Fixed n))) bs p) v <=>
  abi_decode_source_accepts env (ArrayT ty (Fixed n)) (DROP p bs) v
Proof
  simp_tac bool_ss [abi_decode_source_view_def] >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)`
  >- simp[vyper_to_abi_type_def, is_dynamic_def] >>
  `EVERY (\at. ~is_dynamic at) (REPLICATE n (vyper_to_abi_type env ty))` by
    simp[EVERY_REPLICATE] >>
  `SUM (MAP static_length (REPLICATE n (vyper_to_abi_type env ty))) =
    n * static_length (vyper_to_abi_type env ty)` by
    simp[map_replicate, SUM_REPLICATE] >>
  `vyper_decode_valid_enc_tuple (REPLICATE n (vyper_to_abi_type env ty))
      (TAKE (n * static_length (vyper_to_abi_type env ty)) (DROP p bs))
      (TAKE (n * static_length (vyper_to_abi_type env ty)) (DROP p bs)) =
    vyper_decode_valid_enc_tuple (REPLICATE n (vyper_to_abi_type env ty))
      (DROP p bs) (DROP p bs)` by
    metis_tac[abi_decode_static_members_valid_take] >>
  `abi_decode_members (REPLICATE n (vyper_to_abi_type env ty))
      (TAKE (n * static_length (vyper_to_abi_type env ty)) (DROP p bs))
      (TAKE (n * static_length (vyper_to_abi_type env ty)) (DROP p bs)) =
    abi_decode_members (REPLICATE n (vyper_to_abi_type env ty))
      (DROP p bs) (DROP p bs)` by
    metis_tac[abi_decode_static_members_decode_take] >>
  qspecl_then [`n`, `vyper_to_abi_type env ty`] mp_tac abi_decode_array_members >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`n`, `vyper_to_abi_type env ty`] mp_tac abi_decode_static_source_replicate >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  simp_tac (srw_ss()) [abi_decode_source_accepts_def, vyper_to_abi_type_def,
    is_dynamic_def, static_length_def] >>
  once_rewrite_tac [vyper_decode_valid_enc_def, dec_def] >>
  asm_simp_tac (srw_ss()) [LET_THM, abi_decode_members_value]
QED

Theorem abi_decode_fixed_source_head_bound:
  abi_decode_source_accepts env (ArrayT ty (Fixed n)) view v ==>
  n * abi_member_head_size (vyper_to_abi_type env ty) <= LENGTH view
Proof
  simp_tac bool_ss [abi_decode_source_accepts_def] >> strip_tac >>
  qpat_x_assum `vyper_decode_valid_enc _ _` mp_tac >>
  simp_tac (srw_ss()) [vyper_to_abi_type_def, Once vyper_decode_valid_enc_def,
    LET_THM] >> strip_tac >>
  drule abi_valid_array_heads >> simp[]
QED

Theorem abi_decode_fixed_short_head_reject:
  0 < n * abi_member_head_size (vyper_to_abi_type env ty) /\
  LENGTH bs < p + n * abi_member_head_size (vyper_to_abi_type env ty) ==>
  ~(?v. abi_decode_source_accepts env (ArrayT ty (Fixed n))
    (abi_decode_source_view (vyper_to_abi_type env (ArrayT ty (Fixed n))) bs p) v)
Proof
  simp_tac bool_ss [abi_decode_fixed_source_view_accept] >>
  strip_tac >>
  `LENGTH (DROP p bs) < n * abi_member_head_size (vyper_to_abi_type env ty)` by
    metis_tac[abi_decode_positive_head_short_drop] >>
  metis_tac[abi_decode_fixed_source_head_bound, NOT_LESS_EQUAL]
QED

Theorem abi_decode_fixed_rows_view_accept:
  abi_tuple_rows_schema ce env (REPLICATE n (ei,ty,tv,asz,msz)) /\
  evaluate_type env ty = SOME tv /\
  asz = abi_member_head_size (vyper_to_abi_type env ty) /\
  n * asz <= LENGTH (DROP p bs) /\ n < dimword (:256) ==>
  (abi_decode_source_accepts env (ArrayT ty (Fixed n))
    (abi_decode_source_view (vyper_to_abi_type env (ArrayT ty (Fixed n))) bs p) v <=>
   ?vs. abi_tuple_rows_accept env (DROP p bs) 0 (REPLICATE n (ei,ty,tv,asz,msz)) vs /\
     v = ArrayV (make_array_value tv (Fixed n) vs))
Proof
  simp_tac bool_ss [abi_decode_fixed_source_view_accept] >>
  metis_tac[abi_decode_fixed_rows_source]
QED

Theorem abi_decode_fixed_rows_schema:
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty ==>
  abi_tuple_rows_schema ce env
    (REPLICATE n (type_to_abi_dec_info ce.ce_struct_fields ce ty,ty,tv,
      abi_embedded_static_size ce.ce_struct_fields ty,type_memory_bytes ce ty))
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  simp[abi_tuple_rows_schema_def, EVERY_REPLICATE] >>
  metis_tac[abi_decode_coherent_no_zero_array]
QED

Theorem abi_decode_fixed_constructor_layout:
  abi_decoder_coherent ce env ce.ce_struct_fields (ArrayT ty (Fixed n)) atv /\
  assignable_type env (ArrayT ty (Fixed n)) /\
  abi_decode_bytes_widths env (ArrayT ty (Fixed n)) ==>
  ?tv. atv = ArrayTV tv (Fixed n) /\
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    evaluate_type env ty = SOME tv /\
    assignable_type env ty /\ abi_decode_bytes_widths env ty /\ 0 < n /\
    type_memory_bytes ce (ArrayT ty (Fixed n)) = n * type_memory_bytes ce ty /\
    abi_embedded_static_size ce.ce_struct_fields ty =
      abi_member_head_size (vyper_to_abi_type env ty) /\
    0 < abi_embedded_static_size ce.ce_struct_fields ty /\
    abi_embedded_static_size ce.ce_struct_fields ty <= type_memory_bytes ce ty
Proof
  simp_tac bool_ss [abi_decoder_coherent_array_iff] >> strip_tac >>
  `assignable_type env ty /\ abi_decode_bytes_widths env ty` by
    fs[assignable_type_def, abi_decode_bytes_widths_def] >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `0 < n` by
    (fs[abi_decoder_header_def] >> Cases_on `n` >>
     fs[abi_decode_evaluated_zero_fixed_array_excluded]) >>
  qexists_tac `tv` >> simp[] >> conj_tac
  >- gvs[abi_decoder_header_def, type_memory_size_def] >>
  conj_tac >- metis_tac[abi_decode_assignable_embedded_head_positive] >>
  metis_tac[abi_decode_embedded_head_le_memory]
QED

Theorem abi_decode_fixed_array_owned_contract:
  abi_decoder_coherent ce env ce.ce_struct_fields (ArrayT ty (Fixed n)) atv /\
  assignable_type env (ArrayT ty (Fixed n)) /\
  abi_decode_bytes_widths env (ArrayT ty (Fixed n)) /\
  (!tv. abi_decoder_coherent ce env ce.ce_struct_fields ty tv ==>
    abi_decode_owned_child_contract ce env ty tv) ==>
  abi_decode_owned_child_contract ce env (ArrayT ty (Fixed n)) atv
Proof
  strip_tac >> drule_all abi_decode_fixed_constructor_layout >> strip_tac >>
  `abi_decode_owned_child_contract ce env ty tv` by metis_tac[] >>
  qabbrev_tac `rows = REPLICATE n
    (type_to_abi_dec_info ce.ce_struct_fields ce ty,ty,tv,
      abi_embedded_static_size ce.ce_struct_fields ty,type_memory_bytes ce ty)` >>
  `abi_tuple_rows_schema ce env rows` by
    (simp_tac bool_ss [Abbr `rows`] >> irule abi_decode_fixed_rows_schema >> simp[]) >>
  `SUM(MAP abi_tuple_row_abi_width rows) =
      n * abi_embedded_static_size ce.ce_struct_fields ty /\
   SUM(MAP abi_tuple_row_mem_width rows) = type_memory_bytes ce (ArrayT ty (Fixed n)) /\
   SUM(MAP abi_tuple_row_abi_width rows) <= SUM(MAP abi_tuple_row_mem_width rows)` by
    simp[Abbr `rows`, map_replicate, SUM_REPLICATE,
      abi_tuple_row_abi_width_def, abi_tuple_row_mem_width_def] >>
  `type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Fixed n)) =
    DecComplex (is_abi_dynamic ce.ce_struct_fields ty) (MAP abi_tuple_row_code rows)` by
    simp[Abbr `rows`, type_to_abi_dec_info_def, map_replicate,
      abi_tuple_row_code_def, REPLICATE_GENLIST] >>
  simp_tac bool_ss [abi_decode_owned_child_contract_def] >>
  rpt gen_tac >> strip_tac >>
  `type_memory_bytes ce (ArrayT ty (Fixed n)) < dimword (:256)` by
    (fs[abi_decode_context_pre_def] >> decide_tac) >>
  `SUM(MAP abi_tuple_row_abi_width rows) < dimword (:256)` by
    metis_tac[LESS_EQ_LESS_TRANS] >>
  `hi <> Lit 0w /\ eval_operand src s = SOME(n2w pos) /\
    eval_operand hi s = SOME(n2w(LENGTH bs)) /\ pos < dimword(:256) /\
    LENGTH bs < dimword(:256) /\
    SUM(MAP abi_tuple_row_abi_width rows) < dimword(:256) /\
    abi_decoder_operand_live st.cs_next_var src /\
    abi_decoder_operand_live st.cs_next_var hi /\
    fresh_vars_wrt limit_st s /\ abi_decode_entry st s` by
    (fs[abi_decode_context_pre_def, EVERY_DEF] >> decide_tac) >>
  suspend "execute"
QED

Resume abi_decode_fixed_array_owned_contract[execute]:
  `EVERY (\(ei,ty,tv,asz,msz). abi_decode_owned_child_contract ce env ty tv) rows` by
    simp[Abbr `rows`, EVERY_REPLICATE] >>
  `FOLDR (\(_,asz,_) acc. asz+acc) 0 (MAP abi_tuple_row_code rows) =
    SUM(MAP abi_tuple_row_abi_width rows)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> Induct_on `rows` >- simp[] >>
     gen_tac >> PairCases_on `h` >>
     asm_simp_tac (srw_ss()) [MAP, FOLDR, SUM,
       abi_tuple_row_code_def, abi_tuple_row_abi_width_def]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `type_to_abi_dec_info _ _ (ArrayT _ _) = _`
    (fn th => pure_rewrite_tac [th]) >>
  pure_rewrite_tac [abi_decode_complex_phases, comp_ignore_bind_def, comp_bind_def] >>
  qpat_assum `hi <> Lit 0w` (fn th => simp_tac bool_ss [th]) >>
  qpat_assum `FOLDR _ _ _ = _` (fn th => pure_rewrite_tac [th]) >>
  Cases_on `abi_decode_complex_head_guard src hi
    (SUM(MAP abi_tuple_row_abi_width rows)) st` >>
  rename1 `abi_decode_complex_head_guard src hi _ st = (u,ready)` >>
  Cases_on `u` >> asm_simp_tac bool_ss [] >> strip_tac >>
  `pos+SUM(MAP abi_tuple_row_abi_width rows) <= LENGTH bs ==>
    abi_decode_owned_rows_pre ctx func ce env limit_st next scratch sites
      st dst src base_op hi B bs pos d 0 0 rows s` by
    (strip_tac >> irule abi_decode_constructor_rows_pre >>
     asm_simp_tac bool_ss [] >>
     qexistsl_tac [`env`,`atv`,`ArrayT ty (Fixed n)`] >> simp[]) >>
  qpat_x_assum `LET _ _ = ((),last)` mp_tac >>
  qpat_assum `FOLDR _ _ _ = _` (fn th => pure_rewrite_tac [th]) >>
  qpat_assum `abi_decode_complex_head_guard _ _ _ _ = _`
    (fn th => pure_rewrite_tac [th, LET_THM, pairTheory.UNCURRY_DEF]) >>
  BETA_TAC >> strip_tac >>
  drule_all abi_decode_guarded_owned_rows_outcome >> strip_tac
  >- suspend "short_head"
  >- suspend "accept"
  >> suspend "reject"
QED

Resume abi_decode_fixed_array_owned_contract[short_head]:
  simp_tac bool_ss [abi_decode_context_result_def] >> disj2_tac >>
  qexists_tac `u` >> simp[] >>
  rewrite_tac [GSYM NOT_EXISTS_THM] >>
  mp_tac (Q.INST [`p` |-> `pos`] abi_decode_fixed_short_head_reject) >>
  simp_tac bool_ss [vyper_to_abi_type_def] >>
  impl_tac >- (gvs[] >> simp[]) >> simp[]
QED

Resume abi_decode_fixed_array_owned_contract[accept]:
  `SUM(MAP abi_tuple_row_abi_width rows) <= LENGTH(DROP pos bs) /\
    n < dimword(:256)` by
    (drule abi_decode_schema_row_count_bound >> strip_tac >>
     `n < dimword(:256)` by
       ( `LENGTH rows = n` by simp[Abbr `rows`] >>
         metis_tac[LESS_EQ_LESS_TRANS]) >>
     gvs[LENGTH_DROP] >> decide_tac) >>
  `!v. abi_decode_source_accepts env (ArrayT ty (Fixed n))
    (abi_decode_source_view (vyper_to_abi_type env (ArrayT ty (Fixed n))) bs pos) v <=>
    ?vs. abi_tuple_rows_accept env (DROP pos bs) 0 rows vs /\
      v = ArrayV (make_array_value tv (Fixed n) vs)` by
    (gen_tac >> qpat_assum `abi_tuple_rows_schema _ _ _` mp_tac >>
     simp_tac bool_ss [Abbr `rows`] >> strip_tac >>
     irule abi_decode_fixed_rows_view_accept >> simp[] >>
     conj_tac >- (gvs[LENGTH_DROP] >> decide_tac) >>
     qexists_tac `ce` >> gvs[]) >>
  `abi_tuple_rows_accept env (DROP pos bs) 0 rows vs` by
    metis_tac[abi_tuple_rows_values_accept] >>
  `val_in_memory (ArrayTV tv (Fixed n))
    (ArrayV (make_array_value tv (Fixed n) vs)) d t.vs_memory` by
    (irule abi_decode_fixed_rows_memory >> metis_tac[]) >>
  simp_tac bool_ss [abi_decode_context_result_def] >> disj1_tac >>
  qexistsl_tac [`t`,`ArrayV (make_array_value tv (Fixed n) vs)`] >> fs[] >>
  metis_tac[]
QED

Resume abi_decode_fixed_array_owned_contract[reject]:
  `SUM(MAP abi_tuple_row_abi_width rows) <= LENGTH(DROP pos bs) /\
    n < dimword(:256)` by
    (drule abi_decode_schema_row_count_bound >> strip_tac >>
     `n < dimword(:256)` by
       (`LENGTH rows = n` by simp[Abbr `rows`] >>
        metis_tac[LESS_EQ_LESS_TRANS]) >>
     gvs[LENGTH_DROP] >> decide_tac) >>
  `!v. abi_decode_source_accepts env (ArrayT ty (Fixed n))
    (abi_decode_source_view (vyper_to_abi_type env (ArrayT ty (Fixed n))) bs pos) v <=>
    ?vs. abi_tuple_rows_accept env (DROP pos bs) 0 rows vs /\
      v = ArrayV (make_array_value tv (Fixed n) vs)` by
    (gen_tac >> qpat_assum `abi_tuple_rows_schema _ _ _` mp_tac >>
     simp_tac bool_ss [Abbr `rows`] >> strip_tac >>
     irule abi_decode_fixed_rows_view_accept >> simp[] >>
     conj_tac >- (gvs[LENGTH_DROP] >> decide_tac) >>
     qexists_tac `ce` >> gvs[]) >>
  simp_tac bool_ss [abi_decode_context_result_def] >> disj2_tac >>
  qexists_tac `u` >> metis_tac[]
QED

Finalise abi_decode_fixed_array_owned_contract
