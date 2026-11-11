(* Arbitrary observed memory, without canonical ABI encoding premises. *)
Theory calldataReconstruction
Ancestors
  valueEncodingDefs abiDecoderMembers vyperABI contractABI exprLowering entryDecodeProps abiDecoderString abiDecoderCoherence valueEncodingTyping
  valueEncoding valueEncodingProps compileEnv abiEncoder vyperTyping vyperTypeABI vyperValue words list arithmetic

Theorem calldata_observed_bytes_typed:
  n <= maxn /\ mem_word_at d mem = n2w n ==>
  ?v. value_has_type (BaseTV (BytesT (Dynamic maxn))) v /\
      val_wf (BaseTV (BytesT (Dynamic maxn))) v /\
      val_in_memory (BaseTV (BytesT (Dynamic maxn))) v d mem
Proof
  strip_tac >>
  qexists_tac `vyperValue$BytesV (mem_bytes_at (d+32) n mem)` >>
  simp[value_has_type_def, val_in_memory_def] >>
  irule (cj 1 value_has_type_val_wf) >> simp[value_has_type_def]
QED

Theorem calldata_empty_fixed_typed:
  ?v. value_has_type (ArrayTV tv (Fixed 0)) v /\
      val_wf (ArrayTV tv (Fixed 0)) v /\
      val_in_memory (ArrayTV tv (Fixed 0)) v d mem
Proof
  qexists_tac `ArrayV (SArrayV [])` >>
  simp[value_has_type_def, val_wf_def, val_in_memory_def]
QED

Theorem calldata_observed_string_typed:
  n <= maxn /\ mem_word_at d mem = n2w n ==>
  ?v. value_has_type (BaseTV (StringT maxn)) v /\
      val_wf (BaseTV (StringT maxn)) v /\
      val_in_memory (BaseTV (StringT maxn)) v d mem
Proof
  strip_tac >>
  qexists_tac `StringV (MAP (CHR o w2n) (mem_bytes_at (d+32) n mem))` >>
  simp[value_has_type_def, abi_decoder_string_memory] >>
  conj_tac
  >- (irule (cj 1 value_has_type_val_wf) >> simp[value_has_type_def]) >>
  simp[val_in_memory_def]
QED

Theorem calldata_word_representation:
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\ mem_word_at d mem = typed_val_to_w256 tv v ==>
  val_in_memory tv v d mem
Proof
  Cases_on `ty` >> simp[is_word_type_def, evaluate_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> Cases_on `v` >>
  gvs[value_has_type_def, val_in_memory_def, typed_val_to_w256_def,
      is_word_type_def, AllCaseEqs()]
QED

Theorem calldata_observed_word_typed:
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
    cenv.ce_flag_n_members (nsid_to_string nsid) = m) /\
  abi_clamp_ok
    (case type_to_abi_dec_info sfields cenv ty of
       DecPrimWord c => c | _ => NoClamp) w /\
  mem_word_at d mem = w ==>
  ?v. value_has_type tv v /\ val_wf tv v /\ val_in_memory tv v d mem
Proof
  strip_tac >> drule_all word_arg_clamp_inverse >> strip_tac >>
  qexists_tac `v` >> simp[] >> conj_tac
  >- (irule (cj 1 value_has_type_val_wf) >> simp[]) >>
  irule calldata_word_representation >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`tenv`,`ty`] >> simp[]
QED

Theorem calldata_coherent_observed_word_typed:
  abi_decoder_coherent cenv tenv sfields ty tv /\ is_word_type ty /\
  abi_clamp_ok
    (case type_to_abi_dec_info sfields cenv ty of
       DecPrimWord c => c | _ => NoClamp) w /\
  mem_word_at d mem = w ==>
  ?v. value_has_type tv v /\ val_wf tv v /\ val_in_memory tv v d mem
Proof
  strip_tac >>
  `evaluate_type tenv ty = SOME tv` by
    (drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  `!nsid. ty = FlagT nsid ==>
    ?m. FLOOKUP tenv nsid = SOME (FlagArgs m) /\
        cenv.ce_flag_n_members (nsid_to_string nsid) = m` by
    (rpt strip_tac >> gvs[abi_decoder_coherent_flag_iff] >> metis_tac[]) >>
  drule_all word_arg_clamp_inverse_selected >> strip_tac >>
  qexists_tac `v` >> simp[] >> conj_tac
  >- (irule (cj 1 value_has_type_val_wf) >> simp[]) >>
  irule calldata_word_representation >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`tenv`,`ty`] >> simp[]
QED

Theorem calldata_observed_uint256_typed:
  ?v. value_has_type (BaseTV (UintT 256)) v /\
      val_in_memory (BaseTV (UintT 256)) v d mem
Proof
  qexists_tac `IntV (&(w2n (mem_word_at d mem)))` >>
  simp[value_has_type_def, val_in_memory_def, val_to_w256_def,
       integer_wordTheory.i2w_def] >>
  mp_tac (wordsTheory.w2n_lt |> Q.ISPEC `mem_word_at d mem : bytes32`) >>
  simp[dimword_def]
QED

Theorem calldata_observed_uint256_pair_typed:
  ?v. value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v /\
      val_in_memory (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v d mem
Proof
  `w2n (mem_word_at d mem) < 2 ** 256 /\
   w2n (mem_word_at (d+32) mem) < 2 ** 256` by
    (conj_tac >> mp_tac (w2n_lt |> Q.ISPEC `mem_word_at d mem : bytes32`) >>
     mp_tac (w2n_lt |> Q.ISPEC `mem_word_at (d+32) mem : bytes32`) >>
     simp[dimword_def]) >>
  qexists_tac `ArrayV (make_array_value (BaseTV (UintT 256)) (Fixed 2)
    [IntV (&(w2n (mem_word_at d mem)));
     IntV (&(w2n (mem_word_at (d+32) mem)))])` >>
  simp[make_array_value_def, enumerate_static_array_def, default_value_def] >>
  Cases_on `mem_word_at d mem = 0w` >>
  Cases_on `mem_word_at (d+32) mem = 0w` >>
  gvs[value_has_type_def, val_in_memory_def, val_to_w256_def,
       integer_wordTheory.i2w_def, type_memory_size_def, default_value_def] >>
  simp[GSYM dimword_def, w2n_lt] >> rpt strip_tac >>
  `i = 0 \/ i = 1` by decide_tac >> gvs[]
QED

Theorem calldata_elems_index[local]:
  !vs d i. elems_in_memory vs d tv mem /\ i < LENGTH vs ==>
    val_in_memory tv (EL i vs) (d + i * type_memory_size tv) mem
Proof
  Induct >> simp[val_in_memory_def] >> rpt gen_tac >>
  Cases_on `i` >> simp[val_in_memory_def, ADD_CLAUSES] >>
  rpt strip_tac >> first_x_assum drule >>
  disch_then (qspec_then `n` mp_tac) >>
  `d + SUC n * type_memory_size tv = d + type_memory_size tv + n * type_memory_size tv`
    by (rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  asm_rewrite_tac[]
QED

Theorem calldata_enumerate_memory[local]:
  !kvs. kvs_in_memory kvs d tv mem <=>
    !i v. MEM (i,v) kvs ==>
      val_in_memory tv v (d+i*type_memory_size tv) mem
Proof
  Induct >> simp[val_in_memory_def] >> Cases_on `h` >> simp[val_in_memory_def] >>
  metis_tac[]
QED

Theorem calldata_fixed_values_typed_memory:
  LENGTH vs = n /\ EVERY (value_has_type tv) vs /\ elems_in_memory vs d tv mem ==>
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (make_array_value tv (Fixed n) vs)) /\
  val_wf (ArrayTV tv (Fixed n)) (ArrayV (make_array_value tv (Fixed n) vs)) /\
  val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (make_array_value tv (Fixed n) vs)) d mem
Proof
  strip_tac >>
  `value_has_type (ArrayTV tv (Fixed n)) (ArrayV (make_array_value tv (Fixed n) vs))` by
    (simp[make_array_value_def, value_has_type_def, enumerate_static_array_sorted] >>
     irule sparse_has_type_enumerate >> simp[]) >>
  simp[] >> conj_tac
  >- (irule (cj 1 value_has_type_val_wf) >> simp[]) >>
  simp[make_array_value_def, val_in_memory_def, calldata_enumerate_memory] >>
  conj_tac
  >- (simp[MEM_enumerate_static_array_iff] >> rpt strip_tac >> gvs[] >>
      irule calldata_elems_index >> simp[]) >>
  rpt strip_tac >>
  qspecl_then [`default_value tv`,`0`,`vs`,`i`] mp_tac enumerate_static_array_ALOOKUP >>
  simp[] >> strip_tac >>
  `i < LENGTH vs` by simp[] >>
  drule_all calldata_elems_index >> simp[]
QED

Theorem calldata_dynamic_values_typed_memory:
  LENGTH vs <= maxn /\ EVERY (value_has_type tv) vs /\
  elems_in_memory vs (d+32) tv mem /\ mem_word_at d mem = n2w (LENGTH vs) ==>
  value_has_type (ArrayTV tv (Dynamic maxn)) (ArrayV (make_array_value tv (Dynamic maxn) vs)) /\
  val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (make_array_value tv (Dynamic maxn) vs)) /\
  val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (make_array_value tv (Dynamic maxn) vs)) d mem
Proof
  strip_tac >>
  `value_has_type (ArrayTV tv (Dynamic maxn)) (ArrayV (make_array_value tv (Dynamic maxn) vs))` by
    simp[make_array_value_def, value_has_type_def, all_have_type_EVERY] >>
  simp[make_array_value_def, val_in_memory_def] >>
  irule (cj 1 value_has_type_val_wf) >> gvs[make_array_value_def]
QED

Theorem calldata_tuple_typing[local]:
  !tvs vs. LIST_REL value_has_type tvs vs ==> values_have_types tvs vs
Proof
  Induct >> Cases_on `vs` >> simp[value_has_type_def]
QED

Theorem calldata_tuple_values_typed_memory:
  LIST_REL value_has_type tvs vs /\ tuple_in_memory vs tvs d mem ==>
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
  val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) d mem
Proof
  strip_tac >> drule calldata_tuple_typing >> strip_tac >>
  `value_has_type (TupleTV tvs) (ArrayV (TupleV vs))` by simp[value_has_type_def] >>
  simp[val_in_memory_def] >> irule (cj 1 value_has_type_val_wf) >> simp[]
QED

Theorem calldata_struct_typing[local]:
  !ftypes fields.
  LIST_REL (\nt nv. FST nt = FST nv /\ value_has_type (SND nt) (SND nv)) ftypes fields ==>
  struct_has_type ftypes fields
Proof
  Induct >> Cases_on `fields` >> simp[value_has_type_def] >>
  gen_tac >> PairCases_on `h` >> PairCases_on `h'` >> simp[value_has_type_def]
QED

Theorem calldata_struct_values_typed_memory:
  LIST_REL (\nt nv. FST nt = FST nv /\ value_has_type (SND nt) (SND nv)) ftypes fields /\
  fields_in_memory fields ftypes d mem ==>
  value_has_type (StructTV ftypes) (StructV fields) /\
  val_wf (StructTV ftypes) (StructV fields) /\
  val_in_memory (StructTV ftypes) (StructV fields) d mem
Proof
  strip_tac >> drule calldata_struct_typing >> strip_tac >>
  `value_has_type (StructTV ftypes) (StructV fields)` by simp[value_has_type_def] >>
  simp[val_in_memory_def] >> irule (cj 1 value_has_type_val_wf) >> simp[]
QED

Theorem calldata_fixed_witnesses:
  !n d. (!i. i < n ==> ?v. value_has_type tv v /\
    val_in_memory tv v (d+i*type_memory_size tv) mem) ==>
  ?vs. LENGTH vs = n /\ EVERY (value_has_type tv) vs /\ elems_in_memory vs d tv mem
Proof
  Induct >> simp[val_in_memory_def] >> rpt strip_tac >>
  `?v. value_has_type tv v /\ val_in_memory tv v d mem` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `?vs. LENGTH vs = n /\ EVERY (value_has_type tv) vs /\
     elems_in_memory vs (d+type_memory_size tv) tv mem` by
    (first_x_assum irule >> rpt strip_tac >>
     `d + type_memory_size tv + i * type_memory_size tv = d + SUC i * type_memory_size tv`
       by (rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
     simp[] >> first_x_assum irule >> simp[]) >>
  qexists_tac `v::vs` >> simp[val_in_memory_def]
QED

Theorem calldata_tuple_witnesses:
  !tvs d. EVERY (\tv. !d. ?v. value_has_type tv v /\ val_in_memory tv v d mem) tvs ==>
  ?vs. LIST_REL value_has_type tvs vs /\ tuple_in_memory vs tvs d mem
Proof
  Induct >> simp[]
  >- simp[val_in_memory_def] >>
  rpt strip_tac >>
  `?v. value_has_type h v /\ val_in_memory h v d mem` by metis_tac[] >>
  qpat_x_assum `!d. EVERY _ tvs ==> _` (qspec_then `d+type_memory_size h` mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `v::vs` >> simp[val_in_memory_def]
QED

Theorem calldata_struct_witnesses:
  !ftypes d. EVERY (\nt. !d. ?v. value_has_type (SND nt) v /\ val_in_memory (SND nt) v d mem) ftypes ==>
  ?fields. LIST_REL (\nt nv. FST nt = FST nv /\ value_has_type (SND nt) (SND nv)) ftypes fields /\
    fields_in_memory fields ftypes d mem
Proof
  Induct >> simp[]
  >- simp[val_in_memory_def] >>
  gen_tac >> PairCases_on `h` >> simp[] >> rpt strip_tac >>
  `?v. value_has_type h1 v /\ val_in_memory h1 v d mem` by metis_tac[] >>
  qpat_x_assum `!d. EVERY _ ftypes ==> _` (qspec_then `d+type_memory_size h1` mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `(h0,v)::fields` >> simp[val_in_memory_def]
QED

Theorem calldata_clamp_list[local]:
  !xs. dec_infos_need_clamp xs <=> EXISTS (\x. dec_info_needs_clamp (FST x)) xs
Proof
  Induct >> simp[dec_info_needs_clamp_def] >>
  gen_tac >> PairCases_on `h` >> simp[dec_info_needs_clamp_def]
QED

Theorem calldata_unclamped_static_typed:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
  ~is_abi_dynamic ce.ce_struct_fields ty ==>
  !d mem. ?v. value_has_type tv v /\ val_wf tv v /\ val_in_memory tv v d mem
Proof
  ho_match_mp_tac abi_decoder_coherent_strongind >> rpt conj_tac
  >- suspend "scalar"
  >- suspend "flag"
  >- suspend "array"
  >- suspend "tuple"
  >> suspend "struct"
QED

Resume calldata_unclamped_static_typed[scalar]:
  rpt strip_tac >>
  irule (INST_TYPE [alpha |-> ``:string``, beta |-> ``:num``] calldata_observed_word_typed) >>
  qexistsl_tac [`ce`,`sf`,`FEMPTY`,`BaseT bt`,`mem_word_at d mem`] >>
  simp[evaluate_type_def] >> Cases_on `bt` >>
  gvs[is_word_type_def, type_to_abi_dec_info_def, type_to_abi_clamp_def,
      dec_info_needs_clamp_def, needs_clamp_def, abi_clamp_ok_def,
      AllCaseEqs(), COND_RAND, COND_RATOR] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[is_word_type_def, type_to_abi_dec_info_def, type_to_abi_clamp_def,
      dec_info_needs_clamp_def, needs_clamp_def, abi_clamp_ok_def, AllCaseEqs(),
      COND_RAND, COND_RATOR]
QED
Resume calldata_unclamped_static_typed[flag]:
  rpt strip_tac >>
  gvs[type_to_abi_dec_info_def, dec_info_needs_clamp_def, needs_clamp_def,
      COND_RAND, COND_RATOR] >>
  `w2n (mem_word_at d mem) < 2 ** 256` by
    (mp_tac (w2n_lt |> Q.ISPEC `mem_word_at d mem : bytes32`) >> simp[dimword_def]) >>
  qexists_tac `FlagV (w2n (mem_word_at d mem))` >>
  simp[value_has_type_def, val_in_memory_def, val_to_w256_def, val_wf_def, type_memory_size_def]
QED

Resume calldata_unclamped_static_typed[array]:
  rpt strip_tac >> Cases_on `bound` >>
  gvs[type_to_abi_dec_info_def, dec_info_needs_clamp_def] >>
  Cases_on `n = 0`
  >- (gvs[] >> metis_tac[calldata_empty_fixed_typed]) >>
  gvs[calldata_clamp_list, EXISTS_GENLIST, is_abi_dynamic_def] >>
  `~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)` by metis_tac[NOT_ZERO_LT_ZERO] >>
  `!d. ?v. value_has_type tv v /\ val_in_memory tv v d mem` by metis_tac[] >>
  `?vs. LENGTH vs = n /\ EVERY (value_has_type tv) vs /\ elems_in_memory vs d tv mem` by
    (irule calldata_fixed_witnesses >> metis_tac[]) >>
  qexists_tac `ArrayV (make_array_value tv (Fixed n) vs)` >>
  irule calldata_fixed_values_typed_memory >> simp[]
QED
Resume calldata_unclamped_static_typed[tuple]:
  rpt strip_tac >>
  gvs[type_to_abi_dec_info_def, dec_info_needs_clamp_def,
      calldata_clamp_list, EXISTS_MAP, is_abi_dynamic_def] >>
  `EVERY (\tv. !d. ?v. value_has_type tv v /\ val_in_memory tv v d mem) tvs` by
    (gvs[EVERY_EL, LIST_REL_EL_EQN] >> metis_tac[]) >>
  drule calldata_tuple_witnesses >> disch_then (qspec_then `d` strip_assume_tac) >>
  qexists_tac `ArrayV (TupleV vs)` >> irule calldata_tuple_values_typed_memory >> simp[]
QED
Resume calldata_unclamped_static_typed[struct]:
  rpt strip_tac >>
  fs[type_to_abi_dec_info_def, dec_info_needs_clamp_def, calldata_clamp_list, EXISTS_MAP] >>
  `~is_dynamic (vyper_to_abi_type env (StructT nsid))` by metis_tac[abi_decoder_header_def] >>
  fs[Once vyper_to_abi_type_def, is_dynamic_def, vyper_to_abi_types_MAP, EXISTS_MAP] >>
  gvs[dec_info_needs_clamp_def, calldata_clamp_list, EXISTS_MAP, is_dynamic_def] >>
  fs[any_dynamic_EXISTS, EXISTS_MAP] >>
  `EVERY (\nt. !d. ?v. value_has_type (SND nt) v /\ val_in_memory (SND nt) v d mem)
    (ZIP (MAP FST (MAP (\(name,ty,sz). (name,ty)) fields),tvs))` by
    (gvs[EVERY_EL, LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >>
     rpt strip_tac >>
     qpat_x_assum `!n. n < LENGTH tvs ==> abi_decoder_coherent _ _ _ _ _ /\ _`
       (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
     `~is_abi_dynamic ce.ce_struct_fields
       (SND ((\(name,ty,sz). (name,ty)) (EL n fields)))` by
       metis_tac[abi_decoder_coherent_header, abi_decoder_header_def, is_dynamic_def] >>
     qpat_x_assum `!n. n < LENGTH tvs ==> ~dec_info_needs_clamp _`
       (qspec_then `n` mp_tac) >> simp[] >>
     Cases_on `EL n fields` >> rename1 `(fnm, rest)` >>
     Cases_on `rest` >> gvs[] >> metis_tac[]) >>
  drule calldata_struct_witnesses >> disch_then (qspec_then `d` strip_assume_tac) >>
  qexists_tac `StructV fields'` >> irule calldata_struct_values_typed_memory >> simp[]
QED

Finalise calldata_unclamped_static_typed
