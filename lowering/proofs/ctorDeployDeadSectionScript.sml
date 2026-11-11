(* mem_dead_bytes stays inside its value's region and reads only the
 * value's live bytes.
 *)
Theory ctorDeployDeadSection
Ancestors
  ctorDeployDefs immSectionDead immutableSectionRel immutableValue valueEncoding valueEncodingDefs
  structFieldsProps entryStateRel list rich_list

Theorem slot_le[local]:
  !k n s. k < n ==> k * s + s <= n * s
Proof
  rpt strip_tac >>
  `?d. n = k + 1 + d` by (qexists_tac `n - (k + 1)` >> decide_tac) >>
  gvs[arithmeticTheory.RIGHT_ADD_DISTRIB]
QED

Theorem mem_dead_bytes_range:
  (!sec off tv i.
     mem_dead_bytes sec off tv i ==> off <= i /\ i < off + type_memory_size tv) /\
  (!sec off tvs i.
     mem_dead_bytes_list sec off tvs i ==>
     off <= i /\ i < off + type_memory_size_list tvs) /\
  (!sec off fields i.
     mem_dead_bytes_fields sec off fields i ==>
     off <= i /\ i < off + type_memory_size_fields fields)
Proof
  ho_match_mp_tac mem_dead_bytes_ind >>
  rw[mem_dead_bytes_def, type_memory_size_def] >> res_tac >> gvs[] >>
  rename1 `k < n` >>
  drule slot_le >> disch_then (qspec_then `type_memory_size tv` assume_tac) >>
  Cases_on `k < w2n (mem_word_at off sec)` >>
  gvs[arithmeticTheory.LEFT_ADD_DISTRIB] >> res_tac >> decide_tac
QED

Theorem mem_word_at_live_window:
  LENGTH sec2 = LENGTH sec1 /\
  (!j. off <= j /\ j < off + 32 /\ j < LENGTH sec1 ==>
       EL j sec2 = EL j sec1) ==>
  mem_word_at off sec2 = mem_word_at off sec1
Proof
  rpt strip_tac >> simp[mem_word_at_def] >> AP_TERM_TAC >>
  irule LIST_EQ >> simp[LENGTH_TAKE] >> rpt strip_tac >>
  simp[EL_TAKE] >> Cases_on `off + x < LENGTH sec1` >>
  simp[EL_APPEND, EL_DROP, EL_REPLICATE] >>
  first_x_assum irule >> decide_tac
QED

Theorem mem_dead_bytes_header_live:
  (tv = BaseTV (BytesT (Dynamic n)) \/ tv = BaseTV (StringT n) \/
   tv = ArrayTV t (Dynamic n)) /\ off <= j /\ j < off + 32 ==>
  ~mem_dead_bytes sec off tv j
Proof
  rpt strip_tac >> gvs[mem_dead_bytes_def] >>
  drule (cj 1 mem_dead_bytes_range) >> decide_tac
QED

Theorem mem_dead_bytes_header_frame:
  (tv = BaseTV (BytesT (Dynamic n)) \/ tv = BaseTV (StringT n) \/
   tv = ArrayTV t (Dynamic n)) /\
  LENGTH sec2 = LENGTH sec1 /\
  (!j. off <= j /\ j < off + type_memory_size tv /\ j < LENGTH sec1 /\
       ~mem_dead_bytes sec1 off tv j ==> EL j sec2 = EL j sec1) ==>
  mem_word_at off sec2 = mem_word_at off sec1
Proof
  rpt strip_tac >> irule mem_word_at_live_window >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  gvs[type_memory_size_def] >>
  simp[mem_dead_bytes_header_live] >>
  metis_tac[mem_dead_bytes_header_live, arithmeticTheory.LESS_EQ_TRANS,
            arithmeticTheory.LESS_LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]
QED

Theorem mem_region_slot_unique:
  a + k * s <= j /\ j < a + k * s + s /\
  a + l * s <= j /\ j < a + l * s + s ==> k = l
Proof
  rpt strip_tac >>
  Cases_on `k < l`
  >- (drule slot_le >> disch_then (qspec_then `s` assume_tac) >> decide_tac) >>
  Cases_on `l < k`
  >- (drule slot_le >> disch_then (qspec_then `s` assume_tac) >> decide_tac) >>
  decide_tac
QED

Theorem mem_dead_fixed_child_agree:
  k < n /\
  (!j. off <= j /\ j < off + type_memory_size (ArrayTV tv (Fixed n)) /\
       j < LENGTH sec1 /\ ~mem_dead_bytes sec1 off (ArrayTV tv (Fixed n)) j ==>
       EL j sec2 = EL j sec1) ==>
  !j. off + k * type_memory_size tv <= j /\
      j < off + k * type_memory_size tv + type_memory_size tv /\
      j < LENGTH sec1 /\
      ~mem_dead_bytes sec1 (off + k * type_memory_size tv) tv j ==>
      EL j sec2 = EL j sec1
Proof
  rpt strip_tac >> first_x_assum irule >>
  `k * type_memory_size tv + type_memory_size tv <= n * type_memory_size tv`
    by metis_tac[slot_le] >>
  simp[type_memory_size_def] >>
  simp[mem_dead_bytes_def] >> gen_tac >> spose_not_then strip_assume_tac >>
  drule (cj 1 mem_dead_bytes_range) >> strip_tac >>
  `k = k'` by
        (irule mem_region_slot_unique >>
         qexistsl_tac [`off`, `j`, `type_memory_size tv`] >> decide_tac) >> gvs[]
QED

Theorem mem_dead_dynamic_child_agree:
  k < n /\ k < w2n (mem_word_at off sec1) /\
  (!j. off <= j /\ j < off + type_memory_size (ArrayTV tv (Dynamic n)) /\
       j < LENGTH sec1 /\ ~mem_dead_bytes sec1 off (ArrayTV tv (Dynamic n)) j ==>
       EL j sec2 = EL j sec1) ==>
  !j. off + 32 + k * type_memory_size tv <= j /\
      j < off + 32 + k * type_memory_size tv + type_memory_size tv /\
      j < LENGTH sec1 /\
      ~mem_dead_bytes sec1 (off + 32 + k * type_memory_size tv) tv j ==>
      EL j sec2 = EL j sec1
Proof
  rpt strip_tac >> first_x_assum irule >>
  `k * type_memory_size tv + type_memory_size tv <= n * type_memory_size tv`
    by metis_tac[slot_le] >>
  simp[type_memory_size_def] >>
  simp[mem_dead_bytes_def] >> gen_tac >> spose_not_then strip_assume_tac >>
  Cases_on `k' < w2n (mem_word_at off sec1)` >> gvs[]
  >- (drule (cj 1 mem_dead_bytes_range) >> strip_tac >>
      `k = k'` by
        (irule mem_region_slot_unique >>
         qexistsl_tac [`off + 32`, `j`, `type_memory_size tv`] >> decide_tac) >> gvs[]) >>
  gvs[arithmeticTheory.ADD1, arithmeticTheory.LEFT_ADD_DISTRIB] >>
  `k = k'` by
        (irule mem_region_slot_unique >>
         qexistsl_tac [`off + 32`, `j`, `type_memory_size tv`] >> decide_tac) >> gvs[]
QED

Theorem mem_dead_list_head_agree:
  (!j. off <= j /\ j < off + type_memory_size_list (tv::tvs) /\
       j < LENGTH sec1 /\ ~mem_dead_bytes_list sec1 off (tv::tvs) j ==>
       EL j sec2 = EL j sec1) ==>
  !j. off <= j /\ j < off + type_memory_size tv /\ j < LENGTH sec1 /\
      ~mem_dead_bytes sec1 off tv j ==> EL j sec2 = EL j sec1
Proof
  rpt strip_tac >> first_x_assum irule >>
  simp[type_memory_size_def, mem_dead_bytes_def] >>
  spose_not_then strip_assume_tac >>
  drule (cj 2 mem_dead_bytes_range) >> decide_tac
QED

Theorem mem_dead_list_tail_agree:
  (!j. off <= j /\ j < off + type_memory_size_list (tv::tvs) /\
       j < LENGTH sec1 /\ ~mem_dead_bytes_list sec1 off (tv::tvs) j ==>
       EL j sec2 = EL j sec1) ==>
  !j. off + type_memory_size tv <= j /\
      j < off + type_memory_size tv + type_memory_size_list tvs /\
      j < LENGTH sec1 /\
      ~mem_dead_bytes_list sec1 (off + type_memory_size tv) tvs j ==>
      EL j sec2 = EL j sec1
Proof
  rpt strip_tac >> first_x_assum irule >>
  simp[type_memory_size_def, mem_dead_bytes_def] >>
  spose_not_then strip_assume_tac >>
  drule (cj 1 mem_dead_bytes_range) >> decide_tac
QED

Theorem mem_dead_fields_head_agree:
  (!j. off <= j /\ j < off + type_memory_size_fields ((name,tv)::fields) /\
       j < LENGTH sec1 /\ ~mem_dead_bytes_fields sec1 off ((name,tv)::fields) j ==>
       EL j sec2 = EL j sec1) ==>
  !j. off <= j /\ j < off + type_memory_size tv /\ j < LENGTH sec1 /\
      ~mem_dead_bytes sec1 off tv j ==> EL j sec2 = EL j sec1
Proof
  rpt strip_tac >> first_x_assum irule >>
  simp[type_memory_size_def, mem_dead_bytes_def] >>
  spose_not_then strip_assume_tac >>
  drule (cj 3 mem_dead_bytes_range) >> decide_tac
QED

Theorem mem_dead_fields_tail_agree:
  (!j. off <= j /\ j < off + type_memory_size_fields ((name,tv)::fields) /\
       j < LENGTH sec1 /\ ~mem_dead_bytes_fields sec1 off ((name,tv)::fields) j ==>
       EL j sec2 = EL j sec1) ==>
  !j. off + type_memory_size tv <= j /\
      j < off + type_memory_size tv + type_memory_size_fields fields /\
      j < LENGTH sec1 /\
      ~mem_dead_bytes_fields sec1 (off + type_memory_size tv) fields j ==>
      EL j sec2 = EL j sec1
Proof
  rpt strip_tac >> first_x_assum irule >>
  simp[type_memory_size_def, mem_dead_bytes_def] >>
  spose_not_then strip_assume_tac >>
  drule (cj 1 mem_dead_bytes_range) >> decide_tac
QED

Theorem mem_dead_fixed_frame_case:
  (!k sec2. k < n /\ LENGTH sec2 = LENGTH sec1 /\
     (!j. off + k * type_memory_size tv <= j /\
          j < off + k * type_memory_size tv + type_memory_size tv /\
          j < LENGTH sec1 /\ ~mem_dead_bytes sec1 (off + k * type_memory_size tv) tv j
          ==> EL j sec2 = EL j sec1) ==>
     mem_dead_bytes sec2 (off + k * type_memory_size tv) tv =
     mem_dead_bytes sec1 (off + k * type_memory_size tv) tv) ==>
  !sec2. LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size (ArrayTV tv (Fixed n)) /\
         j < LENGTH sec1 /\ ~mem_dead_bytes sec1 off (ArrayTV tv (Fixed n)) j ==>
         EL j sec2 = EL j sec1) ==>
    mem_dead_bytes sec2 off (ArrayTV tv (Fixed n)) =
    mem_dead_bytes sec1 off (ArrayTV tv (Fixed n))
Proof
  rpt strip_tac >>
  `!k. k < n ==> mem_dead_bytes sec2 (off + k * type_memory_size tv) tv =
                       mem_dead_bytes sec1 (off + k * type_memory_size tv) tv`
    by (rpt strip_tac >> first_x_assum irule >>
        metis_tac[mem_dead_fixed_child_agree]) >>
  simp[FUN_EQ_THM, mem_dead_bytes_def] >> metis_tac[]
QED

Theorem mem_dead_dynamic_frame_case:
  (!k sec2. k < n /\ k < w2n (mem_word_at off sec1) /\
     LENGTH sec2 = LENGTH sec1 /\
     (!j. off + 32 + k * type_memory_size tv <= j /\
          j < off + 32 + k * type_memory_size tv + type_memory_size tv /\
          j < LENGTH sec1 /\
          ~mem_dead_bytes sec1 (off + 32 + k * type_memory_size tv) tv j ==>
          EL j sec2 = EL j sec1) ==>
     mem_dead_bytes sec2 (off + 32 + k * type_memory_size tv) tv =
     mem_dead_bytes sec1 (off + 32 + k * type_memory_size tv) tv) ==>
  !sec2. LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size (ArrayTV tv (Dynamic n)) /\
         j < LENGTH sec1 /\ ~mem_dead_bytes sec1 off (ArrayTV tv (Dynamic n)) j ==>
         EL j sec2 = EL j sec1) ==>
    mem_dead_bytes sec2 off (ArrayTV tv (Dynamic n)) =
    mem_dead_bytes sec1 off (ArrayTV tv (Dynamic n))
Proof
  rpt strip_tac >>
  `mem_word_at off sec2 = mem_word_at off sec1`
    by (irule mem_dead_bytes_header_frame >> metis_tac[]) >>
  `!k. k < n /\ k < w2n (mem_word_at off sec1) ==>
       mem_dead_bytes sec2 (off + 32 + k * type_memory_size tv) tv =
       mem_dead_bytes sec1 (off + 32 + k * type_memory_size tv) tv`
    by (rpt strip_tac >> first_x_assum irule >>
        metis_tac[mem_dead_dynamic_child_agree]) >>
  gvs[FUN_EQ_THM] >> simp[mem_dead_bytes_def] >> metis_tac[]
QED

Theorem mem_dead_list_frame_case:
  (!sec2. LENGTH sec2 = LENGTH sec1 /\
     (!j. off <= j /\ j < off + type_memory_size tv /\ j < LENGTH sec1 /\
          ~mem_dead_bytes sec1 off tv j ==> EL j sec2 = EL j sec1) ==>
     mem_dead_bytes sec2 off tv = mem_dead_bytes sec1 off tv) /\
  (!sec2. LENGTH sec2 = LENGTH sec1 /\
     (!j. off + type_memory_size tv <= j /\
          j < off + type_memory_size tv + type_memory_size_list tvs /\
          j < LENGTH sec1 /\
          ~mem_dead_bytes_list sec1 (off + type_memory_size tv) tvs j ==>
          EL j sec2 = EL j sec1) ==>
     mem_dead_bytes_list sec2 (off + type_memory_size tv) tvs =
     mem_dead_bytes_list sec1 (off + type_memory_size tv) tvs) ==>
  !sec2. LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size_list (tv::tvs) /\
         j < LENGTH sec1 /\ ~mem_dead_bytes_list sec1 off (tv::tvs) j ==>
         EL j sec2 = EL j sec1) ==>
    mem_dead_bytes_list sec2 off (tv::tvs) = mem_dead_bytes_list sec1 off (tv::tvs)
Proof
  rpt strip_tac >>
  `mem_dead_bytes sec2 off tv = mem_dead_bytes sec1 off tv`
    by (first_x_assum irule >> metis_tac[mem_dead_list_head_agree]) >>
  `mem_dead_bytes_list sec2 (off + type_memory_size tv) tvs =
   mem_dead_bytes_list sec1 (off + type_memory_size tv) tvs`
    by (first_x_assum irule >> metis_tac[mem_dead_list_tail_agree]) >>
  simp[FUN_EQ_THM, mem_dead_bytes_def]
QED

Theorem mem_dead_fields_frame_case:
  (!sec2. LENGTH sec2 = LENGTH sec1 /\
     (!j. off <= j /\ j < off + type_memory_size tv /\ j < LENGTH sec1 /\
          ~mem_dead_bytes sec1 off tv j ==> EL j sec2 = EL j sec1) ==>
     mem_dead_bytes sec2 off tv = mem_dead_bytes sec1 off tv) /\
  (!sec2. LENGTH sec2 = LENGTH sec1 /\
     (!j. off + type_memory_size tv <= j /\
          j < off + type_memory_size tv + type_memory_size_fields fields /\
          j < LENGTH sec1 /\
          ~mem_dead_bytes_fields sec1 (off + type_memory_size tv) fields j ==>
          EL j sec2 = EL j sec1) ==>
     mem_dead_bytes_fields sec2 (off + type_memory_size tv) fields =
     mem_dead_bytes_fields sec1 (off + type_memory_size tv) fields) ==>
  !sec2. LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size_fields ((name,tv)::fields) /\
         j < LENGTH sec1 /\ ~mem_dead_bytes_fields sec1 off ((name,tv)::fields) j ==>
         EL j sec2 = EL j sec1) ==>
    mem_dead_bytes_fields sec2 off ((name,tv)::fields) =
    mem_dead_bytes_fields sec1 off ((name,tv)::fields)
Proof
  rpt strip_tac >>
  `mem_dead_bytes sec2 off tv = mem_dead_bytes sec1 off tv`
    by (first_x_assum irule >> metis_tac[mem_dead_fields_head_agree]) >>
  `mem_dead_bytes_fields sec2 (off + type_memory_size tv) fields =
   mem_dead_bytes_fields sec1 (off + type_memory_size tv) fields`
    by (first_x_assum irule >> metis_tac[mem_dead_fields_tail_agree]) >>
  simp[FUN_EQ_THM, mem_dead_bytes_def]
QED

Theorem mem_dead_bytes_frame_mutual:
  (!sec1 off tv (i:num). !sec2.
    LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size tv /\ j < LENGTH sec1 /\
         ~mem_dead_bytes sec1 off tv j ==> EL j sec2 = EL j sec1) ==>
    mem_dead_bytes sec2 off tv = mem_dead_bytes sec1 off tv) /\
  (!sec1 off tvs (i:num). !sec2.
    LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size_list tvs /\ j < LENGTH sec1 /\
         ~mem_dead_bytes_list sec1 off tvs j ==> EL j sec2 = EL j sec1) ==>
    mem_dead_bytes_list sec2 off tvs = mem_dead_bytes_list sec1 off tvs) /\
  (!sec1 off fields (i:num). !sec2.
    LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size_fields fields /\ j < LENGTH sec1 /\
         ~mem_dead_bytes_fields sec1 off fields j ==> EL j sec2 = EL j sec1) ==>
    mem_dead_bytes_fields sec2 off fields = mem_dead_bytes_fields sec1 off fields)
Proof
  ho_match_mp_tac mem_dead_bytes_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`mem_dead_bytes _ _ (ArrayTV _ (Fixed _)) = _`]
    >- (rpt strip_tac >> irule mem_dead_fixed_frame_case >> metis_tac[])
  >~ [`mem_dead_bytes _ _ (ArrayTV _ (Dynamic _)) = _`]
    >- (rpt strip_tac >> irule mem_dead_dynamic_frame_case >> metis_tac[])
  >~ [`mem_dead_bytes_list _ _ (_::_) = _`]
    >- (rpt strip_tac >> irule mem_dead_list_frame_case >> simp[])
  >~ [`mem_dead_bytes_fields _ _ (_::_) = _`]
    >- (rpt strip_tac >> irule mem_dead_fields_frame_case >> simp[])
  >~ [`mem_dead_bytes _ _ (BaseTV (BytesT (Dynamic _))) = _`]
    >- (rpt strip_tac >>
        `mem_word_at off sec2 = mem_word_at off sec1`
          by metis_tac[mem_dead_bytes_header_frame] >>
        simp[FUN_EQ_THM, mem_dead_bytes_def])
  >~ [`mem_dead_bytes _ _ (BaseTV (StringT _)) = _`]
    >- (rpt strip_tac >>
        `mem_word_at off sec2 = mem_word_at off sec1`
          by metis_tac[mem_dead_bytes_header_frame] >>
        simp[FUN_EQ_THM, mem_dead_bytes_def]) >>
  simp[FUN_EQ_THM, mem_dead_bytes_def, type_memory_size_def]
QED

(* mem_dead_bytes reads only the length words its value's live bytes hold. *)
Theorem mem_dead_bytes_frame:
  !sec1 sec2 off tv.
    LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size tv /\ j < LENGTH sec1 /\
         ~mem_dead_bytes sec1 off tv j ==> EL j sec2 = EL j sec1) ==>
    mem_dead_bytes sec2 off tv = mem_dead_bytes sec1 off tv
Proof
  metis_tac[cj 1 mem_dead_bytes_frame_mutual]
QED
