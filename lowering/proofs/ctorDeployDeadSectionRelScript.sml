(* immutables_section_rel ignores the immutables section's dead bytes. *)
Theory ctorDeployDeadSectionRel
Ancestors
  ctorDeployDeadSection ctorDeployDefs immutableSectionRel immutableValue
  immutableEncoding valueEncoding valueEncodingDefs compileVyper structFieldsProps entryStateRel
  list rich_list vyperValue words arithmetic vyperTyping alist valueEncodingProofs
  valueTypingMemoryProps exprSimAggregateEncoding immutableEncodingProofs valueEncodingProps

Theorem section_used_mask_transport:
  immutable_value_bytes_rel tv v b1 /\
  LENGTH b2 = type_memory_size tv /\
  (!j. j < type_memory_size tv /\ EL j (immutable_value_mask tv v) ==>
       EL j b2 = EL j b1) ==>
  immutable_value_bytes_rel tv v b2
Proof
  simp[immutable_value_bytes_rel_def, EVERY_EL, EL_ZIP] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!n. n < _ ==> _` (qspec_then `n` mp_tac) >> simp[EL_ZIP]
QED

Theorem section_slice_agreement:
  off + len <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
  (!j. off <= j /\ j < off + len ==> EL j sec2 = EL j sec1) ==>
  mem_bytes_at off len sec2 = mem_bytes_at off len sec1
Proof
  strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
  simp[EL_mem_bytes_at]
QED

Theorem section_word_agreement:
  off + 32 <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
  (!j. off <= j /\ j < off + 32 ==> EL j sec2 = EL j sec1) ==>
  mem_word_at off sec2 = mem_word_at off sec1
Proof
  strip_tac >> drule_all section_slice_agreement >>
  simp[mem_word_at_def, mem_bytes_at_def]
QED

Theorem section_tuple_head_live:
  off <= j /\ j < off + type_memory_size tv /\
  ~mem_dead_bytes sec off tv j ==>
  ~mem_dead_bytes_list sec off (tv::tvs) j
Proof
  simp[mem_dead_bytes_def] >> rpt strip_tac >>
  drule (cj 2 mem_dead_bytes_range) >> simp[]
QED

Theorem section_tuple_tail_live:
  off + type_memory_size tv <= j /\
  ~mem_dead_bytes_list sec (off + type_memory_size tv) tvs j ==>
  ~mem_dead_bytes_list sec off (tv::tvs) j
Proof
  simp[mem_dead_bytes_def] >> rpt strip_tac >>
  drule (cj 1 mem_dead_bytes_range) >> simp[]
QED

Theorem section_fields_head_live:
  off <= j /\ j < off + type_memory_size tv /\
  ~mem_dead_bytes sec off tv j ==>
  ~mem_dead_bytes_fields sec off ((name,tv)::fields) j
Proof
  simp[mem_dead_bytes_def] >> rpt strip_tac >>
  drule (cj 3 mem_dead_bytes_range) >> simp[]
QED

Theorem section_fields_tail_live:
  off + type_memory_size tv <= j /\
  ~mem_dead_bytes_fields sec (off + type_memory_size tv) fields j ==>
  ~mem_dead_bytes_fields sec off ((name,tv)::fields) j
Proof
  simp[mem_dead_bytes_def] >> rpt strip_tac >>
  drule (cj 1 mem_dead_bytes_range) >> simp[]
QED

Theorem section_fixed_child_live:
  off + k * type_memory_size tv <= j /\
  j < off + (k + 1) * type_memory_size tv /\
  ~mem_dead_bytes sec (off + k * type_memory_size tv) tv j ==>
  ~mem_dead_bytes sec off (ArrayTV tv (Fixed n)) j
Proof
  strip_tac >> pure_rewrite_tac[mem_dead_bytes_def] >>
  spose_not_then strip_assume_tac >>
  drule (cj 1 mem_dead_bytes_range) >> strip_tac >>
  `k = k'` by
    (irule mem_region_slot_unique >>
     qexistsl [`off`, `j`, `type_memory_size tv`] >>
     gvs[arithmeticTheory.ADD1, arithmeticTheory.RIGHT_ADD_DISTRIB]) >> gvs[]
QED

Theorem section_dynamic_child_live:
  k < w2n (mem_word_at off sec) /\
  off + 32 + k * type_memory_size tv <= j /\
  j < off + 32 + (k + 1) * type_memory_size tv /\
  ~mem_dead_bytes sec (off + 32 + k * type_memory_size tv) tv j ==>
  ~mem_dead_bytes sec off (ArrayTV tv (Dynamic n)) j
Proof
  strip_tac >> pure_rewrite_tac[mem_dead_bytes_def] >>
  spose_not_then strip_assume_tac >>
  Cases_on `k' < w2n (mem_word_at off sec)` >> gvs[]
  >- (drule (cj 1 mem_dead_bytes_range) >> strip_tac >>
      `k = k'` by
        (irule mem_region_slot_unique >>
         qexistsl [`off + 32`, `j`, `type_memory_size tv`] >>
         gvs[arithmeticTheory.RIGHT_ADD_DISTRIB]) >> gvs[]) >>
  `k = k'` by
    (irule mem_region_slot_unique >>
     qexistsl [`off + 32`, `j`, `type_memory_size tv`] >>
     gvs[arithmeticTheory.RIGHT_ADD_DISTRIB]) >> gvs[]
QED

Theorem section_dynamic_header_live:
  j < off + 32 ==>
  ~mem_dead_bytes sec off (ArrayTV tv (Dynamic n)) j
Proof
  strip_tac >> pure_rewrite_tac[mem_dead_bytes_def] >>
  spose_not_then strip_assume_tac >>
  Cases_on `k < w2n (mem_word_at off sec)` >> gvs[] >>
  drule (cj 1 mem_dead_bytes_range) >> simp[]
QED

Theorem section_mask_fit_used:
  j < n /\ EL j (immutable_mask_fit n mask) ==>
  j < LENGTH mask /\ EL j mask
Proof
  strip_tac >> gvs[immutable_mask_fit_def, EL_TAKE] >>
  Cases_on `j < LENGTH mask` >>
  gvs[EL_APPEND1, EL_APPEND2, EL_REPLICATE]
QED

Theorem section_string_length_word:
  well_formed_type_value (BaseTV (StringT cap)) /\
  (immutable_value_admissible (BaseTV (StringT cap)) (StringV text) \/
   StringV text = default_value (BaseTV (StringT cap))) /\
  val_in_memory (BaseTV (StringT cap)) (StringV text) off sec ==>
  w2n (mem_word_at off sec) = LENGTH text
Proof
  simp[well_formed_type_value_def, immutable_value_admissible_def,
       default_value_def, val_in_memory_def] >>
  rpt strip_tac >> gvs[wordsTheory.w2n_n2w] >>
  irule arithmeticTheory.LESS_MOD >> decide_tac
QED

Theorem section_bytes_length_word:
  well_formed_type_value (BaseTV (BytesT (Dynamic cap))) /\
  (immutable_value_admissible (BaseTV (BytesT (Dynamic cap))) (BytesV bs) \/
   BytesV bs = default_value (BaseTV (BytesT (Dynamic cap)))) /\
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) off sec ==>
  w2n (mem_word_at off sec) = LENGTH bs
Proof
  simp[well_formed_type_value_def, immutable_value_admissible_def,
       default_value_def, val_in_memory_def] >>
  rpt strip_tac >> gvs[wordsTheory.w2n_n2w] >>
  irule arithmeticTheory.LESS_MOD >> decide_tac
QED

Theorem section_dynamic_length_word:
  well_formed_type_value (ArrayTV tv (Dynamic cap)) /\
  (immutable_value_admissible (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) \/
   ArrayV (DynArrayV vs) = default_value (ArrayTV tv (Dynamic cap))) /\
  val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off sec ==>
  w2n (mem_word_at off sec) = LENGTH vs
Proof
  simp[well_formed_type_value_def, immutable_value_admissible_def,
       default_value_def, val_in_memory_def] >>
  rpt strip_tac >> gvs[wordsTheory.w2n_n2w] >>
  irule arithmeticTheory.LESS_MOD >> decide_tac
QED

Theorem section_string_support:
  well_formed_type_value (BaseTV (StringT cap)) /\
  (immutable_value_admissible (BaseTV (StringT cap)) (StringV text) \/
   StringV text = default_value (BaseTV (StringT cap))) /\
  val_in_memory (BaseTV (StringT cap)) (StringV text) off sec ==>
  !j. j < type_memory_size (BaseTV (StringT cap)) /\
      EL j (immutable_value_mask (BaseTV (StringT cap)) (StringV text)) ==>
      ~mem_dead_bytes sec off (BaseTV (StringT cap)) (off + j)
Proof
  strip_tac >>
  `w2n (mem_word_at off sec) = LENGTH text` by
    (irule section_string_length_word >> qexists_tac `cap` >> simp[]) >>
  simp[immutable_value_mask_def] >> rpt strip_tac >>
  drule_all section_mask_fit_used >> strip_tac >>
  gvs[mem_dead_bytes_def]
QED

Theorem section_bytes_support:
  well_formed_type_value (BaseTV (BytesT (Dynamic cap))) /\
  (immutable_value_admissible (BaseTV (BytesT (Dynamic cap))) (BytesV bs) \/
   BytesV bs = default_value (BaseTV (BytesT (Dynamic cap)))) /\
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) off sec ==>
  !j. j < type_memory_size (BaseTV (BytesT (Dynamic cap))) /\
      EL j (immutable_value_mask (BaseTV (BytesT (Dynamic cap))) (BytesV bs)) ==>
      ~mem_dead_bytes sec off (BaseTV (BytesT (Dynamic cap))) (off + j)
Proof
  strip_tac >>
  `w2n (mem_word_at off sec) = LENGTH bs` by
    (irule section_bytes_length_word >> qexists_tac `cap` >> simp[]) >>
  simp[immutable_value_mask_def] >> rpt strip_tac >>
  drule_all section_mask_fit_used >> strip_tac >>
  gvs[mem_dead_bytes_def]
QED

Theorem section_base_support:
  well_formed_type_value (BaseTV bt) /\
  (immutable_value_admissible (BaseTV bt) v \/ v = default_value (BaseTV bt)) /\
  val_in_memory (BaseTV bt) v off sec ==>
  !j. j < type_memory_size (BaseTV bt) /\
      EL j (immutable_value_mask (BaseTV bt) v) ==>
      ~mem_dead_bytes sec off (BaseTV bt) (off + j)
Proof
  Cases_on `bt`
  >~ [`StringT cap`]
  >- (Cases_on `v` >> simp[immutable_value_admissible_def, default_value_def] >>
      strip_tac >> rename1 `StringV text` >> gen_tac >> strip_tac >>
      once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
      irule section_string_support >> simp[] >> qexists_tac `text` >>
      simp[immutable_value_admissible_def, default_value_def])
  >~ [`BytesT bound`]
  >- (Cases_on `bound` >- simp[mem_dead_bytes_def] >>
      Cases_on `v` >> simp[immutable_value_admissible_def, default_value_def] >>
      strip_tac >> rename1 `BytesV bs` >> gen_tac >> strip_tac >>
      once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
      irule section_bytes_support >> simp[] >> qexists_tac `bs` >>
      simp[immutable_value_admissible_def, default_value_def])
  >> simp[mem_dead_bytes_def]
QED

Theorem section_string_frame:
  well_formed_type_value (BaseTV (StringT cap)) /\
  (immutable_value_admissible (BaseTV (StringT cap)) (StringV text) \/
   StringV text = default_value (BaseTV (StringT cap))) /\
  val_in_memory (BaseTV (StringT cap)) (StringV text) off sec1 /\
  off + type_memory_size (BaseTV (StringT cap)) <= LENGTH sec1 /\
  LENGTH sec2 = LENGTH sec1 /\
  (!j. off <= j /\ j < off + type_memory_size (BaseTV (StringT cap)) /\
       ~mem_dead_bytes sec1 off (BaseTV (StringT cap)) j ==>
       EL j sec2 = EL j sec1) ==>
  val_in_memory (BaseTV (StringT cap)) (StringV text) off sec2
Proof
  strip_tac >>
  `w2n (mem_word_at off sec1) = LENGTH text` by
    (irule section_string_length_word >> qexists_tac `cap` >> simp[]) >>
  `LENGTH text <= cap` by
    gvs[immutable_value_admissible_def, default_value_def] >>
  `LENGTH text <= 32 * word_size cap` by
    metis_tac[word_size_capacity, arithmeticTheory.LESS_EQ_TRANS] >>
  `mem_bytes_at off (32 + LENGTH text) sec2 =
   mem_bytes_at off (32 + LENGTH text) sec1` by
    (irule section_slice_agreement >> gvs[type_memory_size_def] >>
     rpt strip_tac >> first_x_assum irule >> gvs[mem_dead_bytes_def]) >>
  drule mem_bytes_at_agree_window >> strip_tac >>
  gvs[val_in_memory_def]
QED

Theorem section_bytes_frame:
  well_formed_type_value (BaseTV (BytesT (Dynamic cap))) /\
  (immutable_value_admissible (BaseTV (BytesT (Dynamic cap))) (BytesV bs) \/
   BytesV bs = default_value (BaseTV (BytesT (Dynamic cap)))) /\
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) off sec1 /\
  off + type_memory_size (BaseTV (BytesT (Dynamic cap))) <= LENGTH sec1 /\
  LENGTH sec2 = LENGTH sec1 /\
  (!j. off <= j /\ j < off + type_memory_size (BaseTV (BytesT (Dynamic cap))) /\
       ~mem_dead_bytes sec1 off (BaseTV (BytesT (Dynamic cap))) j ==>
       EL j sec2 = EL j sec1) ==>
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) off sec2
Proof
  strip_tac >>
  `w2n (mem_word_at off sec1) = LENGTH bs` by
    (irule section_bytes_length_word >> qexists_tac `cap` >> simp[]) >>
  `LENGTH bs <= cap` by
    gvs[immutable_value_admissible_def, default_value_def] >>
  `LENGTH bs <= 32 * word_size cap` by
    metis_tac[word_size_capacity, arithmeticTheory.LESS_EQ_TRANS] >>
  `mem_bytes_at off (32 + LENGTH bs) sec2 =
   mem_bytes_at off (32 + LENGTH bs) sec1` by
    (irule section_slice_agreement >> gvs[type_memory_size_def] >>
     rpt strip_tac >> first_x_assum irule >> gvs[mem_dead_bytes_def]) >>
  drule mem_bytes_at_agree_window >> strip_tac >> gvs[val_in_memory_def]
QED

Theorem section_base_frame:
  well_formed_type_value (BaseTV bt) /\
  (immutable_value_admissible (BaseTV bt) v \/ v = default_value (BaseTV bt)) /\
  val_in_memory (BaseTV bt) v off sec1 /\
  off + type_memory_size (BaseTV bt) <= LENGTH sec1 /\
  LENGTH sec2 = LENGTH sec1 /\
  (!j. off <= j /\ j < off + type_memory_size (BaseTV bt) /\
       ~mem_dead_bytes sec1 off (BaseTV bt) j ==> EL j sec2 = EL j sec1) ==>
  val_in_memory (BaseTV bt) v off sec2
Proof
  Cases_on `bt`
  >~ [`StringT cap`]
  >- (Cases_on `v` >> simp[immutable_value_admissible_def, default_value_def] >>
      strip_tac >> irule section_string_frame >>
      simp[immutable_value_admissible_def, default_value_def] >>
      qexists_tac `sec1` >> gvs[])
  >~ [`BytesT bound`]
  >- (Cases_on `bound`
      >- (strip_tac >>
          `mem_word_at off sec2 = mem_word_at off sec1` by
            (irule section_word_agreement >>
             gvs[type_memory_size_def, mem_dead_bytes_def]) >>
          Cases_on `v` >> gvs[immutable_value_admissible_def, default_value_def,
                                   val_in_memory_def]) >>
      Cases_on `v` >> simp[immutable_value_admissible_def, default_value_def] >>
      strip_tac >> irule section_bytes_frame >>
      simp[immutable_value_admissible_def, default_value_def] >>
      qexists_tac `sec1` >> gvs[])
  >> strip_tac >>
  `mem_word_at off sec2 = mem_word_at off sec1` by
    (irule section_word_agreement >>
     gvs[type_memory_size_def, mem_dead_bytes_def]) >>
  Cases_on `v` >> gvs[immutable_value_admissible_def, default_value_def,
                           val_in_memory_def]
QED

Theorem section_flag_case:
  well_formed_type_value (FlagTV k) /\
  (immutable_value_admissible (FlagTV k) v \/ v = default_value (FlagTV k)) /\
  val_in_memory (FlagTV k) v off sec1 ==>
  (!j. j < type_memory_size (FlagTV k) /\
       EL j (immutable_value_mask (FlagTV k) v) ==>
       ~mem_dead_bytes sec1 off (FlagTV k) (off + j)) /\
  (!sec2. off + type_memory_size (FlagTV k) <= LENGTH sec1 /\
     LENGTH sec2 = LENGTH sec1 /\
     (!j. off <= j /\ j < off + type_memory_size (FlagTV k) /\
          ~mem_dead_bytes sec1 off (FlagTV k) j ==> EL j sec2 = EL j sec1) ==>
     val_in_memory (FlagTV k) v off sec2)
Proof
  strip_tac >> simp[mem_dead_bytes_def] >> gen_tac >> strip_tac >>
  `mem_word_at off sec2 = mem_word_at off sec1` by
    (irule section_word_agreement >> gvs[type_memory_size_def]) >>
  Cases_on `v` >> gvs[immutable_value_admissible_def, default_value_def,
                           val_in_memory_def]
QED

Theorem section_none_case:
  well_formed_type_value NoneTV /\
  (immutable_value_admissible NoneTV v \/ v = default_value NoneTV) /\
  val_in_memory NoneTV v off sec1 ==>
  (!j. j < type_memory_size NoneTV /\
       EL j (immutable_value_mask NoneTV v) ==>
       ~mem_dead_bytes sec1 off NoneTV (off + j)) /\
  (!sec2. off + type_memory_size NoneTV <= LENGTH sec1 /\
     LENGTH sec2 = LENGTH sec1 /\
     (!j. off <= j /\ j < off + type_memory_size NoneTV /\
          ~mem_dead_bytes sec1 off NoneTV j ==> EL j sec2 = EL j sec1) ==>
     val_in_memory NoneTV v off sec2)
Proof
  Cases_on `v` >> simp[immutable_value_admissible_def, default_value_def,
                            type_memory_size_def, val_in_memory_def]
QED

Theorem section_sparse_child_valid:
  (immutable_value_admissible (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) \/
   ArrayV (SArrayV kvs) = default_value (ArrayTV tv (Fixed n))) ==>
  immutable_value_admissible tv
    (case ALOOKUP kvs i of NONE => default_value tv | SOME x => x) \/
  (case ALOOKUP kvs i of NONE => default_value tv | SOME x => x) = default_value tv
Proof
  simp[immutable_value_admissible_def, default_value_def] >> strip_tac >> gvs[] >>
  Cases_on `ALOOKUP kvs i` >> simp[] >>
  drule ALOOKUP_MEM >> strip_tac >>
  gvs[EVERY_MEM] >> first_x_assum drule >> simp[]
QED

Theorem section_tuple_cons_valid:
  immutable_tuple_admissible (tv::tvs) vs \/ vs = MAP default_value (tv::tvs) ==>
  ?v rest. vs = v::rest /\
    (immutable_value_admissible tv v \/ v = default_value tv) /\
    (immutable_tuple_admissible tvs rest \/ rest = MAP default_value tvs)
Proof
  Cases_on `vs` >> simp[immutable_value_admissible_def] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem section_fields_cons_valid:
  immutable_fields_admissible ((name,tv)::fields) vs \/
  vs = MAP (\(id,t). (id,default_value t)) ((name,tv)::fields) ==>
  ?v rest. vs = (name,v)::rest /\
    (immutable_value_admissible tv v \/ v = default_value tv) /\
    (immutable_fields_admissible fields rest \/
     rest = MAP (\(id,t). (id,default_value t)) fields)
Proof
  namedCases_on `vs` ["", "entry rest"] >> simp[immutable_value_admissible_def] >>
  Cases_on `entry` >>
  simp[immutable_value_admissible_def] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem section_tuple_mask_length_cons[local]:
  (!vs. LENGTH (immutable_tuple_mask tvs vs) = type_memory_size_list tvs) ==>
  !tv vs. LENGTH (immutable_tuple_mask (tv::tvs) vs) = type_memory_size_list (tv::tvs)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `vs` >>
  simp[Once immutable_value_mask_def, type_memory_size_def]
QED

Theorem section_tuple_mask_length:
  !tvs vs. LENGTH (immutable_tuple_mask tvs vs) = type_memory_size_list tvs
Proof
  Induct >- simp[Once immutable_value_mask_def, type_memory_size_def] >>
  drule section_tuple_mask_length_cons >> simp[]
QED

Theorem section_fields_mask_length_cons[local]:
  (!vs. LENGTH (immutable_fields_mask fields vs) = type_memory_size_fields fields) ==>
  !field vs. LENGTH (immutable_fields_mask (field::fields) vs) =
    type_memory_size_fields (field::fields)
Proof
  strip_tac >> qx_gen_tac `entry` >> PairCases_on `entry` >> gen_tac >> Cases_on `vs`
  >- simp[Once immutable_value_mask_def, type_memory_size_def] >>
  PairCases_on `h` >> simp[Once immutable_value_mask_def, type_memory_size_def]
QED

Theorem section_fields_mask_length:
  !fields vs. LENGTH (immutable_fields_mask fields vs) = type_memory_size_fields fields
Proof
  Induct >- simp[Once immutable_value_mask_def, type_memory_size_def] >>
  drule section_fields_mask_length_cons >> simp[]
QED

Theorem section_tuple_cons_support:
  (!off sec. val_in_memory tv v off sec ==>
    !j. j < type_memory_size tv /\ EL j (immutable_value_mask tv v) ==>
      ~mem_dead_bytes sec off tv (off+j)) /\
  (!off sec. tuple_in_memory vs tvs off sec ==>
    !j. j < type_memory_size_list tvs /\ EL j (immutable_tuple_mask tvs vs) ==>
      ~mem_dead_bytes_list sec off tvs (off+j)) ==>
  !off sec. tuple_in_memory (v::vs) (tv::tvs) off sec ==>
    !j. j < type_memory_size_list (tv::tvs) /\
        EL j (immutable_tuple_mask (tv::tvs) (v::vs)) ==>
      ~mem_dead_bytes_list sec off (tv::tvs) (off+j)
Proof
  strip_tac >> simp[val_in_memory_def, Once immutable_value_mask_def,
                        type_memory_size_def] >> rpt gen_tac >> strip_tac >>
  gen_tac >> strip_tac >> Cases_on `j < type_memory_size tv`
  >- (gvs[EL_APPEND1] >> irule section_tuple_head_live >> simp[]) >>
  gvs[EL_APPEND2] >> irule section_tuple_tail_live >> simp[] >>
  qpat_x_assum `!off sec. tuple_in_memory _ _ _ _ ==> _` drule >>
  disch_then (qspec_then `j - type_memory_size tv` mp_tac) >> simp[]
QED

Theorem section_fields_cons_support:
  (!off sec. val_in_memory tv v off sec ==>
    !j. j < type_memory_size tv /\ EL j (immutable_value_mask tv v) ==>
      ~mem_dead_bytes sec off tv (off+j)) /\
  (!off sec. fields_in_memory vs fields off sec ==>
    !j. j < type_memory_size_fields fields /\ EL j (immutable_fields_mask fields vs) ==>
      ~mem_dead_bytes_fields sec off fields (off+j)) ==>
  !off sec. fields_in_memory ((name,v)::vs) ((name,tv)::fields) off sec ==>
    !j. j < type_memory_size_fields ((name,tv)::fields) /\
        EL j (immutable_fields_mask ((name,tv)::fields) ((name,v)::vs)) ==>
      ~mem_dead_bytes_fields sec off ((name,tv)::fields) (off+j)
Proof
  strip_tac >> simp[val_in_memory_def, Once immutable_value_mask_def,
                        type_memory_size_def] >> rpt gen_tac >> strip_tac >>
  gen_tac >> strip_tac >> Cases_on `j < type_memory_size tv`
  >- (gvs[EL_APPEND1] >> irule section_fields_head_live >> simp[]) >>
  gvs[EL_APPEND2] >> irule section_fields_tail_live >> simp[] >>
  qpat_x_assum `!off sec. fields_in_memory _ _ _ _ ==> _` drule >>
  disch_then (qspec_then `j - type_memory_size tv` mp_tac) >> simp[]
QED

Theorem section_tuple_cons_frame:
  (!off sec1 sec2. val_in_memory tv v off sec1 /\
    off + type_memory_size tv <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size tv /\
      ~mem_dead_bytes sec1 off tv j ==> EL j sec2 = EL j sec1) ==>
    val_in_memory tv v off sec2) ==>
  (!off sec1 sec2. tuple_in_memory vs tvs off sec1 /\
    off + type_memory_size_list tvs <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size_list tvs /\
      ~mem_dead_bytes_list sec1 off tvs j ==> EL j sec2 = EL j sec1) ==>
    tuple_in_memory vs tvs off sec2) ==>
  !off sec1 sec2. tuple_in_memory (v::vs) (tv::tvs) off sec1 /\
    off + type_memory_size_list (tv::tvs) <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size_list (tv::tvs) /\
      ~mem_dead_bytes_list sec1 off (tv::tvs) j ==> EL j sec2 = EL j sec1) ==>
    tuple_in_memory (v::vs) (tv::tvs) off sec2
Proof
  disch_tac >> disch_tac >> simp[val_in_memory_def, type_memory_size_def] >> rpt strip_tac
  >- (qpat_x_assum `!off sec1 sec2. val_in_memory _ _ _ _ /\ _ ==> _` irule >>
      qexists_tac `sec1` >> simp[] >> rpt strip_tac >>
      qpat_x_assum `!j. _ ==> EL j sec2 = _` irule >> simp[] >>
      irule section_tuple_head_live >> simp[]) >>
  qpat_x_assum `!off sec1 sec2. tuple_in_memory _ _ _ _ /\ _ ==> _` irule >>
  qexists_tac `sec1` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!j. _ ==> EL j sec2 = _` irule >> simp[] >>
  irule section_tuple_tail_live >> simp[]
QED

Theorem section_fields_cons_frame:
  (!off sec1 sec2. val_in_memory tv v off sec1 /\
    off + type_memory_size tv <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size tv /\
      ~mem_dead_bytes sec1 off tv j ==> EL j sec2 = EL j sec1) ==>
    val_in_memory tv v off sec2) ==>
  (!off sec1 sec2. fields_in_memory vs fields off sec1 /\
    off + type_memory_size_fields fields <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size_fields fields /\
      ~mem_dead_bytes_fields sec1 off fields j ==> EL j sec2 = EL j sec1) ==>
    fields_in_memory vs fields off sec2) ==>
  !off sec1 sec2. fields_in_memory ((name,v)::vs) ((name,tv)::fields) off sec1 /\
    off + type_memory_size_fields ((name,tv)::fields) <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size_fields ((name,tv)::fields) /\
      ~mem_dead_bytes_fields sec1 off ((name,tv)::fields) j ==> EL j sec2 = EL j sec1) ==>
    fields_in_memory ((name,v)::vs) ((name,tv)::fields) off sec2
Proof
  disch_tac >> disch_tac >> simp[val_in_memory_def, type_memory_size_def] >> rpt strip_tac
  >- (qpat_x_assum `!off sec1 sec2. val_in_memory _ _ _ _ /\ _ ==> _` irule >>
      qexists_tac `sec1` >> simp[] >> rpt strip_tac >>
      qpat_x_assum `!j. _ ==> EL j sec2 = _` irule >> simp[] >>
      irule section_fields_head_live >> simp[]) >>
  qpat_x_assum `!off sec1 sec2. fields_in_memory _ _ _ _ /\ _ ==> _` irule >>
  qexists_tac `sec1` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!j. _ ==> EL j sec2 = _` irule >> simp[] >>
  irule section_fields_tail_live >> simp[]
QED

Theorem section_tuple_nil_case:
  immutable_tuple_admissible [] vs \/ vs = MAP default_value [] ==>
  (!off sec j. j < type_memory_size_list [] /\ EL j (immutable_tuple_mask [] vs) ==>
    ~mem_dead_bytes_list sec off [] (off+j)) /\
  (!off sec. tuple_in_memory vs [] off sec)
Proof
  Cases_on `vs` >> simp[immutable_value_admissible_def, type_memory_size_def,
                         val_in_memory_def]
QED

Theorem section_fields_nil_case:
  immutable_fields_admissible [] vs \/ vs = MAP (\(id,t). (id,default_value t)) [] ==>
  (!off sec j. j < type_memory_size_fields [] /\ EL j (immutable_fields_mask [] vs) ==>
    ~mem_dead_bytes_fields sec off [] (off+j)) /\
  (!off sec. fields_in_memory vs [] off sec)
Proof
  Cases_on `vs` >> simp[immutable_value_admissible_def, type_memory_size_def,
                         val_in_memory_def]
QED

Theorem section_tuple_wrapper_support:
  (!off sec. tuple_in_memory vs tvs off sec ==>
    !j. j < type_memory_size_list tvs /\ EL j (immutable_tuple_mask tvs vs) ==>
      ~mem_dead_bytes_list sec off tvs (off+j)) ==>
  !off sec. val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) off sec ==>
    !j. j < type_memory_size (TupleTV tvs) /\
      EL j (immutable_value_mask (TupleTV tvs) (ArrayV (TupleV vs))) ==>
      ~mem_dead_bytes sec off (TupleTV tvs) (off+j)
Proof
  strip_tac >> simp[val_in_memory_def, Once immutable_value_mask_def,
                        type_memory_size_def, mem_dead_bytes_def] >>
  rpt strip_tac >> drule_all section_mask_fit_used >> strip_tac >>
  first_x_assum drule >> disch_then (qspec_then `j` mp_tac) >> simp[]
QED

Theorem section_fields_wrapper_support:
  (!off sec. fields_in_memory vs fields off sec ==>
    !j. j < type_memory_size_fields fields /\ EL j (immutable_fields_mask fields vs) ==>
      ~mem_dead_bytes_fields sec off fields (off+j)) ==>
  !off sec. val_in_memory (StructTV fields) (StructV vs) off sec ==>
    !j. j < type_memory_size (StructTV fields) /\
      EL j (immutable_value_mask (StructTV fields) (StructV vs)) ==>
      ~mem_dead_bytes sec off (StructTV fields) (off+j)
Proof
  strip_tac >> simp[val_in_memory_def, Once immutable_value_mask_def,
                        type_memory_size_def, mem_dead_bytes_def] >>
  rpt strip_tac >> drule_all section_mask_fit_used >> strip_tac >>
  first_x_assum drule >> disch_then (qspec_then `j` mp_tac) >> simp[]
QED

Theorem section_tuple_wrapper_frame:
  (!off sec1 sec2. tuple_in_memory vs tvs off sec1 /\
    off + type_memory_size_list tvs <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size_list tvs /\
      ~mem_dead_bytes_list sec1 off tvs j ==> EL j sec2 = EL j sec1) ==>
    tuple_in_memory vs tvs off sec2) ==>
  !off sec1 sec2. val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) off sec1 /\
    off + type_memory_size (TupleTV tvs) <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size (TupleTV tvs) /\
      ~mem_dead_bytes sec1 off (TupleTV tvs) j ==> EL j sec2 = EL j sec1) ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) off sec2
Proof
  simp[val_in_memory_def, type_memory_size_def, mem_dead_bytes_def]
QED

Theorem section_fields_wrapper_frame:
  (!off sec1 sec2. fields_in_memory vs fields off sec1 /\
    off + type_memory_size_fields fields <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size_fields fields /\
      ~mem_dead_bytes_fields sec1 off fields j ==> EL j sec2 = EL j sec1) ==>
    fields_in_memory vs fields off sec2) ==>
  !off sec1 sec2. val_in_memory (StructTV fields) (StructV vs) off sec1 /\
    off + type_memory_size (StructTV fields) <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size (StructTV fields) /\
      ~mem_dead_bytes sec1 off (StructTV fields) j ==> EL j sec2 = EL j sec1) ==>
    val_in_memory (StructTV fields) (StructV vs) off sec2
Proof
  simp[val_in_memory_def, type_memory_size_def, mem_dead_bytes_def]
QED

Theorem section_flat_uniform_index:
  EVERY (\bs. LENGTH bs = sz) bss /\ j < LENGTH (FLAT bss) ==>
  ?i k. i < LENGTH bss /\ k < sz /\ j = i * sz + k /\
    EL j (FLAT bss) = EL k (EL i bss)
Proof
  strip_tac >> drule immutable_flat_uniform_length >> strip_tac >>
  `0 < sz` by (Cases_on `sz` >> gvs[]) >>
  `j DIV sz < LENGTH bss` by simp[arithmeticTheory.DIV_LT_X] >>
  `j MOD sz < sz` by simp[] >>
  `j = j DIV sz * sz + j MOD sz` by simp[arithmeticTheory.DIVISION] >>
  drule_all immutable_flat_slot >> strip_tac >>
  qexistsl [`j DIV sz`, `j MOD sz`] >> simp[] >>
  `j MOD sz < LENGTH (EL (j DIV sz) bss)` by
    (gvs[EVERY_EL] >> first_x_assum drule >> simp[]) >>
  qpat_x_assum `FLAT bss = _` SUBST1_TAC >>
  `j - sz * (j DIV sz) = j MOD sz` by
    (gvs[arithmeticTheory.MULT_COMM] >> decide_tac) >>
  simp[EL_APPEND1, EL_APPEND2]
QED

Theorem section_fixed_support:
  (!i. i < n ==> !off sec.
    val_in_memory tv (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
      off sec ==>
    !j. j < type_memory_size tv /\
      EL j (immutable_value_mask tv
        (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)) ==>
      ~mem_dead_bytes sec off tv (off+j)) ==>
  !off sec. val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) off sec ==>
    !j. j < type_memory_size (ArrayTV tv (Fixed n)) /\
      EL j (immutable_value_mask (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs))) ==>
      ~mem_dead_bytes sec off (ArrayTV tv (Fixed n)) (off+j)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> gen_tac >>
  simp[Once immutable_value_mask_def] >> strip_tac >>
  drule_all section_mask_fit_used >> strip_tac >>
  `EVERY (\bs. LENGTH bs = type_memory_size tv)
    (GENLIST (\i. immutable_value_mask tv
      (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)) n)` by
    simp[EVERY_GENLIST] >>
  drule_all section_flat_uniform_index >> simp[] >> strip_tac >> gvs[] >>
  irule section_fixed_child_live >> qexists_tac `i` >>
  simp[arithmeticTheory.RIGHT_ADD_DISTRIB] >>
  `val_in_memory tv
    (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
    (off + i * type_memory_size tv) sec` by
    (gvs[val_in_memory_sarray] >> Cases_on `ALOOKUP kvs i` >> simp[] >>
     metis_tac[kvs_in_memory_lookup]) >>
  qpat_x_assum `!i. i < n ==> _` (qspec_then `i` mp_tac) >> simp[] >>
  disch_then drule >> disch_then (qspec_then `k` mp_tac) >> simp[]
QED

Theorem section_fixed_frame:
  (!i. i < n ==> !off sec1 sec2.
    val_in_memory tv (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v) off sec1 /\
    off + type_memory_size tv <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size tv /\
      ~mem_dead_bytes sec1 off tv j ==> EL j sec2 = EL j sec1) ==>
    val_in_memory tv (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v) off sec2) /\
  (immutable_value_admissible (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) \/
   ArrayV (SArrayV kvs) = default_value (ArrayTV tv (Fixed n))) ==>
  !off sec1 sec2.
    val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) off sec1 /\
    off + type_memory_size (ArrayTV tv (Fixed n)) <= LENGTH sec1 /\
    LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size (ArrayTV tv (Fixed n)) /\
      ~mem_dead_bytes sec1 off (ArrayTV tv (Fixed n)) j ==> EL j sec2 = EL j sec1) ==>
    val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) off sec2
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  rpt gen_tac >> strip_tac >>
  `!i. i < n ==> val_in_memory tv
    (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
    (off + i * type_memory_size tv) sec2` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < n ==> _` (qspec_then `i` mp_tac) >> simp[] >>
     disch_then irule >> qexists_tac `sec1` >>
     `val_in_memory tv
       (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
       (off + i * type_memory_size tv) sec1` by
       (gvs[val_in_memory_sarray] >> Cases_on `ALOOKUP kvs i` >> simp[] >>
        metis_tac[kvs_in_memory_lookup]) >>
     `i * type_memory_size tv + type_memory_size tv <= n * type_memory_size tv` by
       (`(i + 1) * type_memory_size tv <= n * type_memory_size tv` suffices_by
          (rewrite_tac[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >> simp[]) >>
     simp[] >> conj_tac
     >- (rpt strip_tac >> qpat_x_assum `!j. _ ==> EL j sec2 = _` irule >>
         simp[type_memory_size_def] >>
         irule section_fixed_child_live >> qexists_tac `i` >>
         simp[arithmeticTheory.RIGHT_ADD_DISTRIB]) >>
     gvs[type_memory_size_def]) >>
  rewrite_tac[val_in_memory_sarray] >> conj_tac
  >- (rewrite_tac[kvs_in_memory_every, EVERY_MEM] >> rpt gen_tac >>
      PairCases_on `e` >> strip_tac >>
      `e0 < n /\ ALOOKUP kvs e0 = SOME e1` by
        (gvs[immutable_value_admissible_def, default_value_def, EVERY_MEM] >>
         conj_tac
         >- (qpat_x_assum `!e. MEM e kvs ==> _` drule >> simp[]) >>
         irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]) >>
      qpat_x_assum `!i. i < n ==> val_in_memory _ _ _ sec2`
        (qspec_then `e0` mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!i. i < n ==> val_in_memory _ _ _ sec2`
    (qspec_then `i` mp_tac) >> simp[]
QED

Theorem section_dynamic_support:
  (!v. MEM v vs ==> !off sec. val_in_memory tv v off sec ==>
    !j. j < type_memory_size tv /\ EL j (immutable_value_mask tv v) ==>
      ~mem_dead_bytes sec off tv (off+j)) /\
  well_formed_type_value (ArrayTV tv (Dynamic n)) /\
  (immutable_value_admissible (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) \/
   ArrayV (DynArrayV vs) = default_value (ArrayTV tv (Dynamic n))) ==>
  !off sec. val_in_memory (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) off sec ==>
    !j. j < type_memory_size (ArrayTV tv (Dynamic n)) /\
      EL j (immutable_value_mask (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs))) ==>
      ~mem_dead_bytes sec off (ArrayTV tv (Dynamic n)) (off+j)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  rpt gen_tac >> strip_tac >>
  `w2n (mem_word_at off sec) = LENGTH vs` by
    (irule section_dynamic_length_word >> qexistsl [`n`, `tv`] >> simp[]) >>
  gen_tac >> simp[Once immutable_value_mask_def] >> strip_tac >>
  drule_all section_mask_fit_used >> strip_tac >>
  Cases_on `j < 32`
  >- (irule section_dynamic_header_live >> simp[]) >>
  gvs[EL_APPEND2, ETA_THM] >>
  `j - 32 < LENGTH (FLAT (MAP (\a. immutable_value_mask tv a) vs))` by decide_tac >>
  `EVERY (\bs. LENGTH bs = type_memory_size tv)
    (MAP (\a. immutable_value_mask tv a) vs)` by simp[EVERY_MAP, EVERY_MEM] >>
  drule_all section_flat_uniform_index >> simp[] >> strip_tac >>
  `MEM (EL i vs) vs` by simp[EL_MEM] >>
  `val_in_memory tv (EL i vs) (off + 32 + i * type_memory_size tv) sec` by
    (irule elems_in_memory_EL >> gvs[val_in_memory_def, default_value_def]) >>
  irule section_dynamic_child_live >> qexists_tac `i` >>
  simp[arithmeticTheory.RIGHT_ADD_DISTRIB] >>
  `j + off = k + (off + (i * type_memory_size tv + 32))` by decide_tac >>
  qpat_x_assum `!v. MEM v vs ==> _` drule >> disch_then drule >>
  disch_then (qspec_then `k` mp_tac) >> gvs[EL_MAP]
QED

Theorem section_dynamic_frame:
  (!v. MEM v vs ==> !off sec1 sec2.
    val_in_memory tv v off sec1 /\ off + type_memory_size tv <= LENGTH sec1 /\
    LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size tv /\
      ~mem_dead_bytes sec1 off tv j ==> EL j sec2 = EL j sec1) ==>
    val_in_memory tv v off sec2) /\
  well_formed_type_value (ArrayTV tv (Dynamic n)) /\
  (immutable_value_admissible (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) \/
   ArrayV (DynArrayV vs) = default_value (ArrayTV tv (Dynamic n))) ==>
  !off sec1 sec2.
    val_in_memory (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) off sec1 /\
    off + type_memory_size (ArrayTV tv (Dynamic n)) <= LENGTH sec1 /\
    LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size (ArrayTV tv (Dynamic n)) /\
      ~mem_dead_bytes sec1 off (ArrayTV tv (Dynamic n)) j ==> EL j sec2 = EL j sec1) ==>
    val_in_memory (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) off sec2
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  rpt gen_tac >> strip_tac >>
  `w2n (mem_word_at off sec1) = LENGTH vs` by
    (irule section_dynamic_length_word >> qexistsl [`n`, `tv`] >> simp[]) >>
  `LENGTH vs <= n` by
    (gvs[immutable_value_admissible_def, default_value_def]) >>
  `mem_word_at off sec2 = mem_word_at off sec1` by
    (irule section_word_agreement >> simp[] >> conj_tac
     >- (rpt strip_tac >> qpat_x_assum `!j. _ ==> EL j sec2 = _` irule >>
         simp[type_memory_size_def, section_dynamic_header_live]) >>
     gvs[type_memory_size_def]) >>
  simp[val_in_memory_def] >> conj_tac
  >- gvs[val_in_memory_def, default_value_def] >>
  irule elems_in_memory_intro >> gen_tac >> strip_tac >>
  `MEM (EL i vs) vs` by simp[EL_MEM] >>
  qpat_x_assum `!v. MEM v vs ==> _` drule >> disch_then irule >>
  qexists_tac `sec1` >>
  `val_in_memory tv (EL i vs) (off + 32 + i * type_memory_size tv) sec1` by
    (irule elems_in_memory_EL >> gvs[val_in_memory_def, default_value_def]) >>
  `(i + 1) * type_memory_size tv <= n * type_memory_size tv` by simp[] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!j. _ ==> EL j sec2 = _` irule >>
      simp[type_memory_size_def] >>
      irule section_dynamic_child_live >> qexists_tac `i` >>
      simp[arithmeticTheory.RIGHT_ADD_DISTRIB]) >>
  qpat_x_assum `(i + 1) * _ <= _` mp_tac >>
  rewrite_tac[arithmeticTheory.RIGHT_ADD_DISTRIB] >>
  gvs[type_memory_size_def] >> decide_tac
QED

local
val value_prop = ``\tv v. well_formed_type_value tv /\
    (immutable_value_admissible tv v \/ v = default_value tv) ==>
    (!off sec. val_in_memory tv v off sec ==>
      !j. j < type_memory_size tv /\ EL j (immutable_value_mask tv v) ==>
        ~mem_dead_bytes sec off tv (off+j)) /\
    (!off sec1 sec2. val_in_memory tv v off sec1 /\
      off + type_memory_size tv <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
      (!j. off <= j /\ j < off + type_memory_size tv /\
        ~mem_dead_bytes sec1 off tv j ==> EL j sec2 = EL j sec1) ==>
      val_in_memory tv v off sec2)``;
val tuple_prop = ``\tvs vs. EVERY well_formed_type_value tvs /\
    (immutable_tuple_admissible tvs vs \/ vs = MAP default_value tvs) ==>
    (!off sec. tuple_in_memory vs tvs off sec ==>
      !j. j < type_memory_size_list tvs /\ EL j (immutable_tuple_mask tvs vs) ==>
        ~mem_dead_bytes_list sec off tvs (off+j)) /\
    (!off sec1 sec2. tuple_in_memory vs tvs off sec1 /\
      off + type_memory_size_list tvs <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
      (!j. off <= j /\ j < off + type_memory_size_list tvs /\
        ~mem_dead_bytes_list sec1 off tvs j ==> EL j sec2 = EL j sec1) ==>
      tuple_in_memory vs tvs off sec2)``;
val fields_prop = ``\fields vs. EVERY (\(name,tv). well_formed_type_value tv) fields /\
    (immutable_fields_admissible fields vs \/
      vs = MAP (\(name,tv). (name,default_value tv)) fields) ==>
    (!off sec. fields_in_memory vs fields off sec ==>
      !j. j < type_memory_size_fields fields /\ EL j (immutable_fields_mask fields vs) ==>
        ~mem_dead_bytes_fields sec off fields (off+j)) /\
    (!off sec1 sec2. fields_in_memory vs fields off sec1 /\
      off + type_memory_size_fields fields <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
      (!j. off <= j /\ j < off + type_memory_size_fields fields /\
        ~mem_dead_bytes_fields sec1 off fields j ==> EL j sec2 = EL j sec1) ==>
      fields_in_memory vs fields off sec2)``;
in

Theorem section_induction_base_case[local]:
  !bt v. ^value_prop (BaseTV bt) v
Proof
  BETA_TAC >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >> conj_tac
  >- (rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
      irule section_base_support >> simp[] >> qexists_tac `v` >> simp[]) >>
  rpt gen_tac >> strip_tac >> irule section_base_frame >> simp[] >>
  qexists_tac `sec1` >> simp[]
QED

Theorem section_induction_tuple_case[local]:
  !tvs v. (!av vs. v = ArrayV av /\ av = TupleV vs ==> ^tuple_prop tvs vs) ==>
    ^value_prop (TupleTV tvs) v
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  Cases_on `v` >> simp[immutable_value_admissible_def, default_value_def,
    default_value_tuple_MAP] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  simp[immutable_value_admissible_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  first_x_assum (qspec_then `TupleV l` mp_tac) >> simp[] >>
  (impl_tac >- gvs[well_formed_type_value_def, SF ETA_ss]) >>
  strip_tac >> conj_tac
  >- (drule (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM]
        section_tuple_wrapper_support) >> simp[]) >>
  drule section_tuple_wrapper_frame >> simp[]
QED

Theorem section_induction_struct_case[local]:
  !fields v. (!vs. v = StructV vs ==> ^fields_prop fields vs) ==>
    ^value_prop (StructTV fields) v
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  Cases_on `v` >> simp[immutable_value_admissible_def, default_value_def,
    default_value_struct_MAP] >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  first_x_assum (qspec_then `l` mp_tac) >> simp[] >>
  (impl_tac >- (gvs[well_formed_type_value_def, EVERY_MEM,
    pairTheory.FORALL_PROD] >> metis_tac[])) >>
  strip_tac >> conj_tac
  >- (drule (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM]
        section_fields_wrapper_support) >> simp[]) >>
  drule section_fields_wrapper_frame >> simp[]
QED

Theorem section_induction_array_case[local]:
  !tv bound v.
    (!b w av n kvs i.
      (bound,v) = (b,w) /\ w = ArrayV av /\ b = Fixed n /\
      av = SArrayV kvs /\ i < n ==>
      ^value_prop tv (case ALOOKUP kvs i of NONE => default_value tv | SOME x => x)) /\
    (!b w av n vs a.
      (bound,v) = (b,w) /\ w = ArrayV av /\ b = Dynamic n /\
      av = DynArrayV vs /\ MEM a vs ==> ^value_prop tv a) ==>
    ^value_prop (ArrayTV tv bound) v
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  Cases_on `bound` >> Cases_on `v` >>
  simp[immutable_value_admissible_def, default_value_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  simp[immutable_value_admissible_def, default_value_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  rule_assum_tac (SIMP_RULE (srw_ss()) [])
  >~ [`ArrayTV tv (Fixed n)`]
  >- (`!i. immutable_value_admissible tv
         (case ALOOKUP l i of NONE => default_value tv | SOME x => x) \/
         (case ALOOKUP l i of NONE => default_value tv | SOME x => x) = default_value tv` by
        (gen_tac >> mp_tac (Q.INST [`kvs` |-> `l`] section_sparse_child_valid) >>
         simp[immutable_value_admissible_def, default_value_def]) >>
      gs[well_formed_type_value_def, IMP_CONJ_THM, FORALL_AND_THM] >>
      (conj_tac
       >- (mp_tac (Q.INST [`kvs` |-> `l`]
             (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] section_fixed_support)) >>
           asm_rewrite_tac[] >> simp[] >> asm_rewrite_tac[]) >>
       (mp_tac (Q.INST [`kvs` |-> `l`] section_fixed_frame) >>
        simp[immutable_value_admissible_def, default_value_def] >>
        asm_rewrite_tac[]))) >>
  `!x. MEM x l ==> immutable_value_admissible tv x \/ x = default_value tv` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  gs[well_formed_type_value_def, IMP_CONJ_THM, FORALL_AND_THM] >>
  (conj_tac
   >- (mp_tac (Q.INST [`vs` |-> `l`]
         (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] section_dynamic_support)) >>
       simp[immutable_value_admissible_def, default_value_def,
         well_formed_type_value_def] >> asm_rewrite_tac[]) >>
   (mp_tac (Q.INST [`vs` |-> `l`] section_dynamic_frame) >>
    simp[immutable_value_admissible_def, default_value_def,
      well_formed_type_value_def] >> asm_rewrite_tac[]))
QED

Theorem section_induction_tuple_cons_case[local]:
  !tv tvs vs.
    (!v rest. vs = v::rest ==> ^value_prop tv v) /\
    (!v rest. vs = v::rest ==> ^tuple_prop tvs rest) /\
    (vs = [] ==> ^value_prop tv (default_value tv)) /\
    (vs = [] ==> ^tuple_prop tvs []) ==> ^tuple_prop (tv::tvs) vs
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  drule section_tuple_cons_valid >>
  disch_then (qx_choose_then `v` (qx_choose_then `rest`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac))) >>
  qpat_x_assum `(_::_) = [] ==> _` kall_tac >>
  qpat_x_assum `(_::_) = [] ==> _` kall_tac >>
  gs[] >>
  (conj_tac
   >- metis_tac[ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM]
         section_tuple_cons_support]
   >> (mp_tac (Q.INST [`vs` |-> `rest`] section_tuple_cons_frame) >>
       asm_rewrite_tac[]))
QED

Theorem section_induction_fields_cons_case[local]:
  !name tv fields vs.
    (!pair rest id v. vs = pair::rest /\ pair = (id,v) ==> ^value_prop tv v) /\
    (!pair rest id v. vs = pair::rest /\ pair = (id,v) ==> ^fields_prop fields rest) /\
    (vs = [] ==> ^value_prop tv (default_value tv)) /\
    (vs = [] ==> ^fields_prop fields []) ==> ^fields_prop ((name,tv)::fields) vs
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  drule section_fields_cons_valid >>
  disch_then (qx_choose_then `v` (qx_choose_then `rest`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac))) >>
  gs[] >>
  (conj_tac
   >- metis_tac[ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM]
         section_fields_cons_support]
   >> (mp_tac (Q.INST [`vs` |-> `rest`] section_fields_cons_frame) >>
       asm_rewrite_tac[]))
QED

Theorem section_support_frame_induction:
  (!tv v. well_formed_type_value tv /\
    (immutable_value_admissible tv v \/ v = default_value tv) ==>
    (!off sec. val_in_memory tv v off sec ==>
      !j. j < type_memory_size tv /\ EL j (immutable_value_mask tv v) ==>
        ~mem_dead_bytes sec off tv (off+j)) /\
    (!off sec1 sec2. val_in_memory tv v off sec1 /\
      off + type_memory_size tv <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
      (!j. off <= j /\ j < off + type_memory_size tv /\
        ~mem_dead_bytes sec1 off tv j ==> EL j sec2 = EL j sec1) ==>
      val_in_memory tv v off sec2)) /\
  (!tvs vs. EVERY well_formed_type_value tvs /\
    (immutable_tuple_admissible tvs vs \/ vs = MAP default_value tvs) ==>
    (!off sec. tuple_in_memory vs tvs off sec ==>
      !j. j < type_memory_size_list tvs /\ EL j (immutable_tuple_mask tvs vs) ==>
        ~mem_dead_bytes_list sec off tvs (off+j)) /\
    (!off sec1 sec2. tuple_in_memory vs tvs off sec1 /\
      off + type_memory_size_list tvs <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
      (!j. off <= j /\ j < off + type_memory_size_list tvs /\
        ~mem_dead_bytes_list sec1 off tvs j ==> EL j sec2 = EL j sec1) ==>
      tuple_in_memory vs tvs off sec2)) /\
  (!fields vs. EVERY (\(name,tv). well_formed_type_value tv) fields /\
    (immutable_fields_admissible fields vs \/
      vs = MAP (\(name,tv). (name,default_value tv)) fields) ==>
    (!off sec. fields_in_memory vs fields off sec ==>
      !j. j < type_memory_size_fields fields /\ EL j (immutable_fields_mask fields vs) ==>
        ~mem_dead_bytes_fields sec off fields (off+j)) /\
    (!off sec1 sec2. fields_in_memory vs fields off sec1 /\
      off + type_memory_size_fields fields <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
      (!j. off <= j /\ j < off + type_memory_size_fields fields /\
        ~mem_dead_bytes_fields sec1 off fields j ==> EL j sec2 = EL j sec1) ==>
      fields_in_memory vs fields off sec2))
Proof
  ho_match_mp_tac immutable_value_mask_ind >> rpt conj_tac
  >- suspend "base"
  >- suspend "flag"
  >- suspend "none"
  >- suspend "tuple"
  >- suspend "struct"
  >- suspend "array"
  >- suspend "tuple_nil"
  >- suspend "tuple_cons"
  >- suspend "fields_nil"
  >> suspend "fields_cons"
QED

Resume section_support_frame_induction[base]:
  ACCEPT_TAC (BETA_RULE section_induction_base_case)
QED
Resume section_support_frame_induction[flag]:
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  conj_tac >> rpt gen_tac >> strip_tac >>
  drule_all section_flag_case >> metis_tac[]
QED
Resume section_support_frame_induction[none]:
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  conj_tac >> rpt gen_tac >> strip_tac >>
  drule_all section_none_case >> metis_tac[]
QED
Resume section_support_frame_induction[tuple]:
  ACCEPT_TAC (BETA_RULE section_induction_tuple_case)
QED
Resume section_support_frame_induction[struct]:
  ACCEPT_TAC (BETA_RULE section_induction_struct_case)
QED
Resume section_support_frame_induction[array]:
  ACCEPT_TAC (BETA_RULE section_induction_array_case)
QED
Resume section_support_frame_induction[tuple_nil]:
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  drule section_tuple_nil_case >> metis_tac[]
QED
Resume section_support_frame_induction[tuple_cons]:
  ACCEPT_TAC (BETA_RULE section_induction_tuple_cons_case)
QED
Resume section_support_frame_induction[fields_nil]:
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  drule section_fields_nil_case >> metis_tac[]
QED
Resume section_support_frame_induction[fields_cons]:
  ACCEPT_TAC (BETA_RULE section_induction_fields_cons_case)
QED
Finalise section_support_frame_induction
end
Theorem section_value_mask_support:
  well_formed_type_value tv /\
  (immutable_value_admissible tv v \/ v = default_value tv) /\
  val_in_memory tv v off sec /\
  j < type_memory_size tv /\ EL j (immutable_value_mask tv v) ==>
  ~mem_dead_bytes sec off tv (off+j)
Proof
  metis_tac[cj 1 section_support_frame_induction]
QED

Theorem section_value_memory_frame:
  well_formed_type_value tv /\
  (immutable_value_admissible tv v \/ v = default_value tv) /\
  val_in_memory tv v off sec1 /\
  off + type_memory_size tv <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
  (!j. off <= j /\ j < off + type_memory_size tv /\
    ~mem_dead_bytes sec1 off tv j ==> EL j sec2 = EL j sec1) ==>
  val_in_memory tv v off sec2
Proof
  metis_tac[cj 1 section_support_frame_induction]
QED

Theorem section_evaluated_value_mask_support:
  evaluate_type tenv ty = SOME tv /\
  (immutable_value_admissible tv v \/ v = default_value tv) /\
  val_in_memory tv v off sec /\
  j < type_memory_size tv /\ EL j (immutable_value_mask tv v) ==>
  ~mem_dead_bytes sec off tv (off+j)
Proof
  metis_tac[cj 1 evaluate_type_well_formed, section_value_mask_support]
QED

Theorem section_evaluated_value_memory_frame:
  evaluate_type tenv ty = SOME tv /\
  (immutable_value_admissible tv v \/ v = default_value tv) /\
  val_in_memory tv v off sec1 /\
  off + type_memory_size tv <= LENGTH sec1 /\ LENGTH sec2 = LENGTH sec1 /\
  (!j. off <= j /\ j < off + type_memory_size tv /\
    ~mem_dead_bytes sec1 off tv j ==> EL j sec2 = EL j sec1) ==>
  val_in_memory tv v off sec2
Proof
  metis_tac[cj 1 evaluate_type_well_formed, section_value_memory_frame]
QED

Theorem section_sparse_string_default:
  val_in_memory (ArrayTV (BaseTV (StringT 40)) (Fixed 1))
    (ArrayV (SArrayV [])) off sec ==>
  mem_word_at off sec = 0w
Proof
  simp[val_in_memory_def, default_value_def] >>
  disch_then (qspec_then `0` mp_tac) >> simp[]
QED

Theorem section_sparse_string_mask_probe:
  immutable_value_mask (ArrayTV (BaseTV (StringT 40)) (Fixed 1))
    (ArrayV (SArrayV [])) = REPLICATE 32 T ++ REPLICATE 64 F /\
  immutable_value_admissible (BaseTV (StringT 40))
    (default_value (BaseTV (StringT 40)))
Proof
  EVAL_TAC
QED

Theorem section_declaration_positions_cons[local]:
  (!d post pre2 d2 post2.
     pre ++ d::post = pre2 ++ d2::post2 ==>
     (pre = pre2 /\ d = d2) \/
     (?mid. pre2 = pre ++ d::mid) \/ (?mid. pre = pre2 ++ d2::mid)) ==>
  !d post pre2 d2 post2.
    (h::pre) ++ d::post = pre2 ++ d2::post2 ==>
    (h::pre = pre2 /\ d = d2) \/
    (?mid. pre2 = (h::pre) ++ d::mid) \/
    (?mid. h::pre = pre2 ++ d2::mid)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `pre2` >> simp[] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem section_declaration_positions[local]:
  !pre d post pre2 d2 post2.
    pre ++ d::post = pre2 ++ d2::post2 ==>
    (pre = pre2 /\ d = d2) \/
    (?mid. pre2 = pre ++ d::mid) \/
    (?mid. pre = pre2 ++ d2::mid)
Proof
  Induct >- (rpt gen_tac >> Cases_on `pre2` >> simp[]) >>
  drule section_declaration_positions_cons >> simp[]
QED

Theorem section_declared_size[local]:
  immutables_section_rel tops imms sec /\
  (!pre vis name ty slot post tv v.
     tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
     FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) ==>
     evaluate_type (type_env tops) ty = SOME tv) ==>
  !pre vis name ty slot post tv.
    tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
    evaluate_type (type_env tops) ty = SOME tv ==>
    type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
      type_memory_size tv
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `immutables_section_rel _ _ _` mp_tac >>
  rewrite_tac[immutables_section_rel_def] >> strip_tac >>
  qpat_x_assum `!pre vis name ty slot post. _ ==> ?tv v. _` drule >> strip_tac >>
  qpat_x_assum `!pre vis name ty slot post tv v. _` drule_all >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem section_slots_overlap[local]:
  pre ++ VariableDecl vis Immutable name ty slot :: post =
    pre2 ++ VariableDecl vis2 Immutable name2 ty2 slot2 :: post2 /\
  compute_immutables_len sft pre <= j /\
  j < compute_immutables_len sft pre + type_mem_bytes sft ty /\
  compute_immutables_len sft pre2 <= j /\
  j < compute_immutables_len sft pre2 + type_mem_bytes sft ty2 ==>
  pre = pre2 /\
  VariableDecl vis Immutable name ty slot =
    VariableDecl vis2 Immutable name2 ty2 slot2
Proof
  strip_tac >> drule section_declaration_positions >> strip_tac >> gvs[] >>
  gvs[compute_immutables_len_append, compute_immutables_len_def]
QED

Theorem section_dead_in_slot[local]:
  immutables_section_rel tops imms sec /\
  (!pre vis name ty slot post tv v.
     tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
     FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) ==>
     evaluate_type (type_env tops) ty = SOME tv) /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  evaluate_type (type_env tops) ty = SOME tv /\
  compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre <= j /\
  j < compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre +
        type_memory_size tv /\
  imm_section_dead tops sec j ==>
  mem_dead_bytes sec
    (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre) tv j
Proof
  strip_tac >> drule_all section_declared_size >> disch_tac >>
  qpat_x_assum `imm_section_dead _ _ _` mp_tac >>
  rewrite_tac[imm_section_dead_def] >> strip_tac >>
  drule (cj 1 mem_dead_bytes_range) >> strip_tac >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
     type_memory_size tv` by metis_tac[] >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty' =
     type_memory_size tv'` by
    (irule section_declared_size >> metis_tac[]) >>
  `pre = pre' /\ VariableDecl vis Immutable name ty slot =
     VariableDecl vis' Immutable name' ty' slot'` by
    (irule section_slots_overlap >> metis_tac[]) >>
  qpat_x_assum `tops = _` kall_tac >>
  qpat_x_assum `tops = _` kall_tac >> gvs[]
QED

Theorem section_slot_live_agreement:
  immutables_section_rel tops imms sec1 /\
  (!pre vis name ty slot post tv v.
     tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
     FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) ==>
     evaluate_type (type_env tops) ty = SOME tv) /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) /\
  (!j. j < LENGTH sec1 /\ ~imm_section_dead tops sec1 j ==>
       EL j sec2 = EL j sec1) ==>
  !j. compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre <= j /\
      j < compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre +
            type_memory_size tv /\
      ~mem_dead_bytes sec1
        (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre) tv j ==>
      EL j sec2 = EL j sec1
Proof
  strip_tac >> drule_all immutables_section_rel_lookup >> strip_tac >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!j. j < LENGTH sec1 /\ _ ==> _` irule >>
  reverse conj_tac >- decide_tac >>
  strip_tac >> qpat_x_assum `~mem_dead_bytes _ _ _ _` mp_tac >>
  simp[] >> irule section_dead_in_slot >> metis_tac[]
QED

(* A section related to the immutables stays related when its dead bytes
   change, provided each immutable's recorded type is its declared one. *)
Theorem immutables_section_rel_dead:
  !tops imms sec1 sec2.
    immutables_section_rel tops imms sec1 /\
    (!pre vis name ty slot post tv v.
       tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
       FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) ==>
       evaluate_type (type_env tops) ty = SOME tv) /\
    LENGTH sec2 = LENGTH sec1 /\
    (!j. j < LENGTH sec1 /\ ~imm_section_dead tops sec1 j ==>
         EL j sec2 = EL j sec1) ==>
    immutables_section_rel tops imms sec2
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[immutables_section_rel_def] >> conj_tac
  >- metis_tac[immutables_section_rel_length] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `immutables_section_rel _ _ _`
    (mp_tac o REWRITE_RULE [immutables_section_rel_def]) >> strip_tac >>
  qpat_x_assum `!pre vis name ty slot post. _` drule >> strip_tac >>
  drule_all immutables_section_rel_lookup >> strip_tac >>
  mp_tac section_slot_live_agreement >>
  (impl_tac >- asm_rewrite_tac[]) >> disch_tac >>
  qpat_x_assum `!pre vis name ty slot post tv v. _` drule_all >> disch_tac >>
  qpat_x_assum `tops = _` kall_tac >>
  qexistsl [`tv`, `v`] >> asm_rewrite_tac[] >> conj_tac
  >- (irule section_evaluated_value_memory_frame >>
      conj_tac >- metis_tac[] >> conj_tac >- simp[] >>
      qexists_tac `sec1` >> gs[]) >>
  irule section_used_mask_transport >> (conj_tac >- simp[]) >>
  qexists_tac `mem_bytes_at
    (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre)
    (type_memory_size tv) sec1` >> simp[] >>
  rpt strip_tac >> simp[EL_mem_bytes_at] >>
  qpat_x_assum `!j. _ /\ _ /\ ~mem_dead_bytes _ _ _ _ ==> _` irule >>
  simp[] >>
  metis_tac[arithmeticTheory.ADD_COMM, section_evaluated_value_mask_support]
QED

(* Certify this theory's own proofs, including all exported helpers. *)
val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("Unclosed dead-section relation theorem: " ^ name)
  end) (DB.thms "ctorDeployDeadSectionRel");
