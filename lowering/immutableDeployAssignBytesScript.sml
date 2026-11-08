(* Meaningful-byte interface for immutable assignment stores. *)
Theory immutableDeployAssignBytes
Ancestors
  immutableValue immutableEncoding immutableEncodingProofs valueEncodingProofs
  abiEncoderMemory abiCanonicalHeadSize valueTypingMemoryProps
  valueEncoding immutableDeployAssignAdmissible vyperTyping
  exprSimAggregateEncoding list rich_list

Theorem immutable_mask_prefix_agreement:
  !n k actual expected.
    LENGTH actual = n /\ LENGTH expected = n /\
    TAKE k actual = TAKE k expected ==>
    EVERY (\(used,(a,e)). used ==> a = e)
      (ZIP (TAKE n (REPLICATE k T ++ REPLICATE n F),
            ZIP (actual,expected)))
Proof
  rpt strip_tac >> simp[EVERY_EL, EL_ZIP, EL_TAKE] >>
  rpt strip_tac >>
  Cases_on `n' < k` >> gvs[EL_APPEND_EQN, EL_REPLICATE] >>
  qpat_x_assum `TAKE k actual = TAKE k expected`
    (mp_tac o AP_TERM ``EL n'``) >>
  simp[EL_TAKE]
QED

Theorem immutable_payload_prefix[local]:
  LENGTH bs = k /\ k + 32 <= cap /\
  mem_word_at off mem = n2w k /\
  mem_bytes_at (off+32) k mem = bs ==>
  TAKE (k + 32) (mem_bytes_at off cap mem) =
  TAKE (k + 32)
    (immutable_fit cap (word_to_bytes (n2w k:bytes32) T ++ bs))
Proof
  rpt strip_tac >> gvs[] >>
  drule_all abi_encoder_bytes_source_prefix >> strip_tac >>
  `TAKE (LENGTH bs + 32) (mem_bytes_at off cap mem) =
    mem_bytes_at off (LENGTH bs + 32) mem` by
    metis_tac[mem_bytes_at_window, DROP_0, arithmeticTheory.ADD_CLAUSES] >>
  simp[immutable_fit_def, TAKE_TAKE, arithmeticTheory.ADD_COMM,
       TAKE_APPEND1, TAKE_LENGTH_ID_rwt] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem immutable_base_memory_bytes:
  immutable_value_admissible (BaseTV bt) v /\
  val_in_memory (BaseTV bt) v off mem ==>
  immutable_value_bytes_rel (BaseTV bt) v
    (mem_bytes_at off (type_memory_size (BaseTV bt)) mem)
Proof
  let val base_case =
  Cases_on `v` >>
  simp[immutable_value_admissible_def, val_in_memory_def] >>
  rpt strip_tac >>
  simp[immutable_value_bytes_rel_def, immutable_value_mask_def,
       encode_immutable_value_def, type_memory_size_def,
       immutable_word_fit, immutable_mask_fit_def,
       typed_val_to_w256_def, mem_bytes_at_word,
       TAKE_APPEND1, TAKE_LENGTH_ID_rwt] >>
  simp[immutable_word_bytes_def, immutable_mask_same_bytes] >>
  match_mp_tac immutable_mask_prefix_agreement >>
  simp[] >>
  irule immutable_payload_prefix >> simp[] >>
  mp_tac (Q.SPEC `n` word_size_capacity) >> decide_tac
  in
    Cases_on `bt` >~ [`BytesT b`]
    >- (Cases_on `b` >> base_case)
    >> base_case
  end
QED

Theorem immutable_masked_memory_append:
  LENGTH bytes1 = n /\ LENGTH bytes2 = m /\
  LENGTH mask1 = n /\ LENGTH mask2 = m /\
  EVERY (\(used,(a,e)). used ==> a = e)
    (ZIP (mask1, ZIP (mem_bytes_at off n mem, bytes1))) /\
  EVERY (\(used,(a,e)). used ==> a = e)
    (ZIP (mask2, ZIP (mem_bytes_at (off + n) m mem, bytes2))) ==>
  EVERY (\(used,(a,e)). used ==> a = e)
    (ZIP (mask1 ++ mask2,
      ZIP (mem_bytes_at off (n + m) mem, bytes1 ++ bytes2)))
Proof
  rpt strip_tac >>
  gvs[mem_bytes_at_split_padded, GSYM ZIP_APPEND, EVERY_APPEND,
      arithmeticTheory.ADD_COMM]
QED

Theorem immutable_masked_memory_genlist:
  !n off masks bytes.
    (!i. i < n ==>
      LENGTH (masks i) = k /\ LENGTH (bytes i) = k /\
      EVERY (\(used,(a,e)). used ==> a = e)
        (ZIP (masks i, ZIP (mem_bytes_at (off + i*k) k mem, bytes i)))) ==>
    EVERY (\(used,(a,e)). used ==> a = e)
      (ZIP (FLAT (GENLIST masks n),
        ZIP (mem_bytes_at off (n*k) mem, FLAT (GENLIST bytes n))))
Proof
  Induct >- simp[mem_bytes_at_def] >>
  rpt gen_tac >> strip_tac >>
  simp[GENLIST_CONS, arithmeticTheory.MULT] >>
  irule immutable_masked_memory_append >>
  `!i. i < n ==> LENGTH ((bytes o SUC) i) = k /\ LENGTH ((masks o SUC) i) = k` by
    (simp[] >> metis_tac[arithmeticTheory.LESS_MONO_EQ]) >>
  `LENGTH (FLAT (GENLIST (bytes o SUC) n)) = n*k` by
    (`EVERY (\bs. LENGTH bs = k) (GENLIST (bytes o SUC) n)` by simp[EVERY_GENLIST] >>
     metis_tac[immutable_flat_uniform_length, LENGTH_GENLIST]) >>
  `LENGTH (FLAT (GENLIST (masks o SUC) n)) = n*k` by
    (`EVERY (\bs. LENGTH bs = k) (GENLIST (masks o SUC) n)` by simp[EVERY_GENLIST] >>
     metis_tac[immutable_flat_uniform_length, LENGTH_GENLIST]) >>
  qpat_assum `!i. i < SUC n ==> _` (qspec_then `0` assume_tac) >>
  gvs[] >>
  conj_tac
  >- (qpat_x_assum `!i. i < SUC n ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  qpat_x_assum `!a b c. _` irule >>
  rpt gen_tac >> strip_tac >>
  `SUC i < SUC n` by decide_tac >>
  qpat_x_assum `!i. i < SUC n ==> _` (qspec_then `SUC i` mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  `off + SUC i * k = (off + k) + i*k` by
    (rewrite_tac[arithmeticTheory.MULT] >> decide_tac) >>
  fs[]
QED

Theorem immutable_memory_bytes_mutual:
  (!tv v off mem.
    well_formed_type_value tv /\ immutable_value_admissible tv v /\
    val_in_memory tv v off mem ==>
    immutable_value_bytes_rel tv v (mem_bytes_at off (type_memory_size tv) mem)) /\
  (!tvs vs off mem.
    EVERY well_formed_type_value tvs /\ immutable_tuple_admissible tvs vs /\
    tuple_in_memory vs tvs off mem ==>
    EVERY (\(used,(a,e)). used ==> a = e)
      (ZIP (immutable_tuple_mask tvs vs,
        ZIP (mem_bytes_at off (type_memory_size_list tvs) mem,
             encode_immutable_tuple tvs vs)))) /\
  (!fts vs off mem.
    EVERY (well_formed_type_value o SND) fts /\ immutable_fields_admissible fts vs /\
    fields_in_memory vs fts off mem ==>
    EVERY (\(used,(a,e)). used ==> a = e)
      (ZIP (immutable_fields_mask fts vs,
        ZIP (mem_bytes_at off (type_memory_size_fields fts) mem,
             encode_immutable_fields fts vs))))
Proof
  ho_match_mp_tac type_memory_size_ind >> rpt conj_tac
  >- metis_tac[immutable_base_memory_bytes]
  >- metis_tac[immutable_base_memory_bytes]
  >- metis_tac[immutable_base_memory_bytes]
  >- metis_tac[immutable_base_memory_bytes]
  >- metis_tac[immutable_base_memory_bytes]
  >- metis_tac[immutable_base_memory_bytes]
  >- metis_tac[immutable_base_memory_bytes]
  >- metis_tac[immutable_base_memory_bytes]
  >- (rpt gen_tac >> Cases_on `v` >>
      simp[immutable_value_admissible_def, val_in_memory_def,
           immutable_value_bytes_rel_def, immutable_value_mask_def,
           encode_immutable_value_def, type_memory_size_def,
           immutable_word_fit, typed_val_to_w256_def, mem_bytes_at_word,
           immutable_word_bytes_def, immutable_mask_same_bytes])
  >- simp[immutable_value_bytes_rel_def, type_memory_size_def,
          immutable_value_mask_def, encode_immutable_value_def, mem_bytes_at_def]
  >- suspend "tuple_value"
  >- suspend "fixed"
  >- suspend "dynamic"
  >- suspend "struct_value"
  >- simp[immutable_value_mask_def, encode_immutable_value_def,
          type_memory_size_def, mem_bytes_at_def]
  >- suspend "tuple_cons"
  >- simp[immutable_value_mask_def, encode_immutable_value_def,
          type_memory_size_def, mem_bytes_at_def]
  >> suspend "fields_cons"
QED

Resume immutable_memory_bytes_mutual[tuple_value]:
  `!tvs vs. LENGTH (immutable_tuple_mask tvs vs) = type_memory_size_list tvs` by
    (Induct >> gen_tac >> Cases_on `vs` >>
     simp[Once immutable_value_mask_def, type_memory_size_def]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> Cases_on `v` >>
  simp[immutable_value_admissible_def] >> Cases_on `a` >>
  simp[immutable_value_admissible_def, val_in_memory_def,
       immutable_value_bytes_rel_def, immutable_value_mask_def,
       encode_immutable_value_def, well_formed_type_value_def,
       type_memory_size_def, immutable_fit_exact, immutable_tuple_length,
       immutable_mask_fit_def,
       TAKE_APPEND1, TAKE_LENGTH_ID_rwt, SF ETA_ss] >> metis_tac[]
QED

Resume immutable_memory_bytes_mutual[struct_value]:
  `!fts vs. LENGTH (immutable_fields_mask fts vs) = type_memory_size_fields fts` by
    (Induct >> gen_tac >> simp[Once immutable_value_mask_def, type_memory_size_def] >>
     PairCases_on `h` >> Cases_on `vs` >>
     simp[Once immutable_value_mask_def, type_memory_size_def] >>
     PairCases_on `h` >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> Cases_on `v` >>
  simp[immutable_value_admissible_def, val_in_memory_def,
       immutable_value_bytes_rel_def, immutable_value_mask_def,
       encode_immutable_value_def, well_formed_type_value_def,
       type_memory_size_def, immutable_fit_exact, immutable_fields_length,
       immutable_mask_fit_def,
       TAKE_APPEND1, TAKE_LENGTH_ID_rwt, SF ETA_ss] >> metis_tac[]
QED

Resume immutable_memory_bytes_mutual[tuple_cons]:
  `!tvs vs. LENGTH (immutable_tuple_mask tvs vs) = type_memory_size_list tvs` by
    (Induct >> gen_tac >> Cases_on `vs` >>
     simp[Once immutable_value_mask_def, type_memory_size_def]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> Cases_on `vs` >>
  simp[immutable_value_admissible_def, val_in_memory_def,
       immutable_value_mask_def, encode_immutable_value_def, type_memory_size_def] >>
  strip_tac >>
  `immutable_value_bytes_rel tv h (mem_bytes_at off (type_memory_size tv) mem)` by
    (first_x_assum irule >> simp[]) >>
  irule immutable_masked_memory_append >>
  simp[immutable_tuple_length] >>
  gvs[immutable_value_bytes_rel_def]
QED
Resume immutable_memory_bytes_mutual[fields_cons]:
  `!fts vs. LENGTH (immutable_fields_mask fts vs) = type_memory_size_fields fts` by
    (Induct >> gen_tac >> simp[Once immutable_value_mask_def, type_memory_size_def] >>
     PairCases_on `h` >> Cases_on `vs` >>
     simp[Once immutable_value_mask_def, type_memory_size_def] >>
     PairCases_on `h` >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> Cases_on `vs` >>
  simp[immutable_value_admissible_def] >> PairCases_on `h` >>
  simp[immutable_value_admissible_def, val_in_memory_def,
       immutable_value_mask_def, encode_immutable_value_def, type_memory_size_def] >>
  strip_tac >> gvs[] >>
  `immutable_value_bytes_rel tv h1 (mem_bytes_at off (type_memory_size tv) mem)` by
    (first_x_assum irule >> simp[]) >>
  irule immutable_masked_memory_append >>
  simp[immutable_fields_length] >>
  gvs[immutable_value_bytes_rel_def]
QED
Resume immutable_memory_bytes_mutual[fixed]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> Cases_on `v` >>
  simp[immutable_value_admissible_def] >> Cases_on `a` >>
  simp[immutable_value_admissible_def, val_in_memory_def,
       well_formed_type_value_def] >> strip_tac >>
  `LENGTH (FLAT (GENLIST (\i. immutable_value_mask tv
      (case ALOOKUP l i of NONE => default_value tv | SOME x => x)) n)) =
      n * type_memory_size tv` by
    (irule EQ_TRANS >>
     qexists `LENGTH (GENLIST (\i. immutable_value_mask tv
       (case ALOOKUP l i of NONE => default_value tv | SOME x => x)) n) * type_memory_size tv` >>
     conj_tac >- (irule immutable_flat_uniform_length >> simp[EVERY_GENLIST]) >> simp[]) >>
  `LENGTH (FLAT (GENLIST (\i. case ALOOKUP l i of
       NONE => REPLICATE (type_memory_size tv) 0w | SOME x => encode_immutable_value tv x) n)) =
      n * type_memory_size tv` by
    (irule EQ_TRANS >>
     qexists `LENGTH (GENLIST (\i. case ALOOKUP l i of
       NONE => REPLICATE (type_memory_size tv) 0w | SOME x => encode_immutable_value tv x) n) * type_memory_size tv` >>
     conj_tac >- (irule immutable_flat_uniform_length >> simp[EVERY_GENLIST] >> gen_tac >> strip_tac >> CASE_TAC >> simp[]) >> simp[]) >>
  simp[immutable_value_bytes_rel_def, immutable_value_mask_def,
       encode_immutable_value_def, type_memory_size_def, immutable_fit_exact,
       immutable_mask_fit_def, TAKE_APPEND1, TAKE_LENGTH_ID_rwt] >>
  irule immutable_masked_memory_genlist >>
  gen_tac >> strip_tac >> Cases_on `ALOOKUP l i` >> simp[]
  >- (`immutable_value_admissible tv (default_value tv)` by
        metis_tac[default_immutable_admissible] >>
      `val_in_memory tv (default_value tv) 0 (REPLICATE (type_memory_size tv) 0w)` by
        (mp_tac (cj 1 immutable_default_zero_decodes_mutual) >>
         disch_then (qspecl_then [`tv`, `[]`, `[]`] mp_tac) >> simp[]) >>
      `immutable_value_bytes_rel tv (default_value tv)
         (mem_bytes_at 0 (type_memory_size tv) (REPLICATE (type_memory_size tv) 0w))` by
        (first_x_assum irule >> simp[]) >>
      `immutable_value_bytes_rel tv (default_value tv)
         (mem_bytes_at (off + i * type_memory_size tv) (type_memory_size tv) mem)` by
        (first_x_assum irule >> simp[]) >>
      `val_in_memory tv (default_value tv)
         (off + i * type_memory_size tv) mem` by metis_tac[] >>
      gvs[immutable_value_bytes_rel_def, mem_bytes_at_def, EVERY_EL, EL_ZIP,
          TAKE_APPEND1, EL_TAKE] >>
      metis_tac[]) >>
  `MEM (i,x) l` by metis_tac[alistTheory.ALOOKUP_MEM] >>
  `immutable_value_admissible tv x` by
    (fs[EVERY_MEM] >>
     qpat_x_assum `!e. MEM e l ==> _` (qspec_then `(i,x)` mp_tac) >> simp[]) >>
  `val_in_memory tv x (off + i * type_memory_size tv) mem` by
    metis_tac[kvs_in_memory_lookup] >>
  first_x_assum (drule_all_then mp_tac) >>
  simp[immutable_value_bytes_rel_def]
QED
Resume immutable_memory_bytes_mutual[dynamic]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> Cases_on `v` >>
  simp[immutable_value_admissible_def] >> Cases_on `a` >>
  simp[immutable_value_admissible_def, val_in_memory_def,
       well_formed_type_value_def] >> strip_tac >>
  rename1 `elems_in_memory vs (off + 32) tv mem` >>
  `LENGTH (FLAT (MAP (immutable_value_mask tv) vs)) = LENGTH vs * type_memory_size tv` by
    (`EVERY (\bs. LENGTH bs = type_memory_size tv) (MAP (immutable_value_mask tv) vs)` by simp[EVERY_MAP] >>
     drule immutable_flat_uniform_length >> simp[]) >>
  `LENGTH (FLAT (MAP (encode_immutable_value tv) vs)) = LENGTH vs * type_memory_size tv` by
    (`EVERY (\bs. LENGTH bs = type_memory_size tv) (MAP (encode_immutable_value tv) vs)` by simp[EVERY_MAP] >>
     drule immutable_flat_uniform_length >> simp[]) >>
  `EVERY (\(used,(a,e)). used ==> a = e)
      (ZIP (FLAT (MAP (immutable_value_mask tv) vs),
        ZIP (mem_bytes_at (off + 32) (LENGTH vs * type_memory_size tv) mem,
          FLAT (MAP (encode_immutable_value tv) vs))))` by
    (rewrite_tac[GSYM GENLIST_EL_MAP] >>
     irule immutable_masked_memory_genlist >> simp[] >>
     rpt strip_tac >>
     `immutable_value_admissible tv (EL i vs)` by metis_tac[EVERY_EL] >>
     `val_in_memory tv (EL i vs) ((off + 32) + i * type_memory_size tv) mem` by
       metis_tac[elems_in_memory_EL] >>
     first_x_assum (drule_all_then mp_tac) >> simp[immutable_value_bytes_rel_def]) >>
  `EVERY (\(used,(a,e)). used ==> a = e)
      (ZIP (REPLICATE 32 T ++ FLAT (MAP (immutable_value_mask tv) vs),
        ZIP (mem_bytes_at off (32 + LENGTH vs * type_memory_size tv) mem,
          immutable_word_bytes (n2w (LENGTH vs)) ++
            FLAT (MAP (encode_immutable_value tv) vs))))` by
    (irule immutable_masked_memory_append >> simp[] >>
     simp[mem_bytes_at_word, immutable_word_bytes_def,
          immutable_mask_same_bytes]) >>
  simp[immutable_value_bytes_rel_def, immutable_value_mask_def,
       encode_immutable_value_def, type_memory_size_def] >>
  qpat_x_assum `EVERY _ (ZIP (REPLICATE 32 T ++ _, _))` mp_tac >>
  simp[EVERY_EL, EL_ZIP, SF ETA_ss] >> strip_tac >>
  simp[immutable_mask_fit_def, immutable_fit_def, EVERY_EL, EL_ZIP, EL_TAKE,
       SF ETA_ss] >>
  rpt strip_tac >>
  Cases_on `n' < 32 + LENGTH vs * type_memory_size tv`
  >- (gvs[EL_APPEND_EQN] >>
      first_x_assum (qspec_then `n'` mp_tac) >>
      simp[mem_bytes_at_def, EL_TAKE] >>
      Cases_on `n' < LENGTH (DROP off mem)` >>
      gvs[EL_APPEND_EQN, EL_REPLICATE]) >>
  gvs[EL_APPEND_EQN, EL_REPLICATE]
QED
Finalise immutable_memory_bytes_mutual


Theorem immutable_memory_bytes:
  !tv v off mem.
    well_formed_type_value tv /\ immutable_value_admissible tv v /\
    val_in_memory tv v off mem ==>
    immutable_value_bytes_rel tv v (mem_bytes_at off (type_memory_size tv) mem)
Proof
  metis_tac[immutable_memory_bytes_mutual]
QED
