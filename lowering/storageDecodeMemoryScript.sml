(* Byte observations for storage values copied to memory. *)
Theory storageDecodeMemory
Ancestors
  list rich_list words valueEncoding valueEncodingProps compileEnv
  vyperLookupStorage vyperStorage vyperValue accountsRelProps venomMemProps
  exprSimAggregateEncoding vyperTyping valueTypingMemoryProps

Definition copy_bytes_def:
  copy_bytes st bs n D dst mem <=>
    !i b. i < n /\ b < 32 /\ ~D (bs + i) b ==>
      EL b (mem_bytes_at (dst + 32 * i) 32 mem) =
      EL b (word_to_bytes (read_slot st (bs + i)) T)
End

Definition storage_live_memory_def:
  storage_live_memory st bs tv dst mem <=>
    copy_bytes st bs (type_slot_size tv) (dead_bytes st bs tv) dst mem
End

Theorem type_memory_size_slots:
  (!tv. type_memory_size tv = 32 * type_slot_size tv) /\
  (!tvs. type_memory_size_list tvs = 32 * type_slot_size_list tvs) /\
  (!fields. type_memory_size_fields fields = 32 * type_slot_size_fields fields)
Proof
  ho_match_mp_tac type_memory_size_ind >>
  simp[type_memory_size_def, type_slot_size_def,
       arithmeticTheory.LEFT_ADD_DISTRIB]
QED

Theorem copy_bytes_word:
  !dst mem (w:bytes32).
    (!b. b < 32 ==> EL b (mem_bytes_at dst 32 mem) =
                      EL b (word_to_bytes w T)) ==>
    mem_word_at dst mem = w
Proof
  rpt strip_tac >>
  `mem_bytes_at dst 32 mem = word_to_bytes w T` by
    (irule LIST_EQ >> simp[mem_bytes_at_def, LENGTH_TAKE_EQ]) >>
  simp[mem_word_at_def, GSYM mem_bytes_at_def]
QED

Theorem copy_bytes_subregion:
  !st bs n D dst mem off len D'.
    copy_bytes st bs n D dst mem /\ off + len <= n /\
    (!i b. i < len /\ b < 32 /\ ~D' (bs + off + i) b ==>
       ~D (bs + off + i) b) ==>
    copy_bytes st (bs + off) len D' (dst + 32 * off) mem
Proof
  rw[copy_bytes_def] >>
  qpat_x_assum `!i b. i < n /\ _ ==> _`
    (qspecl_then [`off + i`, `b`] mp_tac) >>
  `off + i < n` by decide_tac >>
  rename1 `~D' (bs + (i + off)) b` >>
  `~D (bs + (i + off)) b` by
    (first_x_assum irule >> fs[ETA_THM, combinTheory.o_DEF]) >>
  `off + i = i + off` by decide_tac >>
  `32 * (off + i) = 32 * i + 32 * off` by decide_tac >>
  asm_rewrite_tac[]
QED

Theorem dead_bytes_not_head[local]:
  (!tv st bs b. ~dead_bytes st bs tv bs b) /\
  (!tvs st bs b. ~dead_bytes_list st bs tvs bs b) /\
  (!fs st bs b. ~dead_bytes_fields st bs fs bs b)
Proof
  ho_match_mp_tac type_memory_size_ind >>
  simp[dead_bytes_def, dyn_bytes_dead_def] >>
  rpt strip_tac
  >- (spose_not_then strip_assume_tac >>
      drule (cj 1 dead_bytes_range) >> strip_tac >>
      `i * type_slot_size tv = 0` by decide_tac >> gvs[])
  >- (spose_not_then strip_assume_tac >>
      drule (cj 1 dead_bytes_range) >> simp[])
  >- (drule (cj 2 dead_bytes_range) >> strip_tac >>
      `type_slot_size tv = 0` by decide_tac >> gvs[])
  >> drule (cj 3 dead_bytes_range) >> strip_tac >>
  `type_slot_size tv = 0` by decide_tac >> gvs[]
QED

Theorem storage_live_memory_head:
  !st bs tv dst mem.
    storage_live_memory st bs tv dst mem /\ 0 < type_slot_size tv ==>
    mem_word_at dst mem = read_slot st bs
Proof
  rpt strip_tac >> irule copy_bytes_word >> rpt strip_tac >>
  qpat_x_assum `storage_live_memory _ _ _ _ _` mp_tac >>
  simp[storage_live_memory_def, copy_bytes_def] >>
  disch_then (qspecl_then [`0`, `b`] mp_tac) >>
  simp[dead_bytes_not_head]
QED

(* Split a byte image when each dead mask stays in its own subregion. *)
Theorem copy_bytes_split[local]:
  !st bs n1 n2 D1 D2 dst mem.
    copy_bytes st bs (n1 + n2) (\j b. D1 j b \/ D2 j b) dst mem /\
    (!j b. D1 j b ==> j < bs + n1) /\
    (!j b. D2 j b ==> bs + n1 <= j) ==>
    copy_bytes st bs n1 D1 dst mem /\
    copy_bytes st (bs + n1) n2 D2 (dst + 32 * n1) mem
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (rw[copy_bytes_def] >>
      `~D2 (bs + i) b` by
        (strip_tac >> first_x_assum drule >> decide_tac) >>
      qpat_x_assum `copy_bytes _ _ _ _ _ _` mp_tac >>
      simp[copy_bytes_def] >> disch_then irule >> simp[]) >>
  irule copy_bytes_subregion >>
  qexistsl [`\j b. D1 j b \/ D2 j b`, `n1 + n2`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!j b. D1 j b ==> _` drule >> decide_tac
QED

Definition storage_live_list_def:
  storage_live_list st bs tvs dst mem <=>
    copy_bytes st bs (type_slot_size_list tvs)
      (dead_bytes_list st bs tvs) dst mem
End

Definition storage_live_fields_def:
  storage_live_fields st bs fs dst mem <=>
    copy_bytes st bs (type_slot_size_fields fs)
      (dead_bytes_fields st bs fs) dst mem
End

Theorem storage_live_list_cons[local]:
  !st bs tv tvs dst mem.
    storage_live_list st bs (tv::tvs) dst mem ==>
    storage_live_memory st bs tv dst mem /\
    storage_live_list st (bs + type_slot_size tv) tvs
      (dst + 32 * type_slot_size tv) mem
Proof
  rpt gen_tac >>
  rewrite_tac[storage_live_list_def, storage_live_memory_def,
    type_slot_size_def] >>
  `dead_bytes_list st bs (tv::tvs) =
     (\j b. dead_bytes st bs tv j b \/
       dead_bytes_list st (bs + type_slot_size tv) tvs j b)` by
    simp[FUN_EQ_THM, dead_bytes_def] >>
  pop_assum SUBST1_TAC >> strip_tac >> irule copy_bytes_split >> simp[] >>
  conj_tac >> rpt strip_tac
  >- (drule (cj 1 dead_bytes_range) >> simp[]) >>
  drule (cj 2 dead_bytes_range) >> simp[]
QED

Theorem storage_live_fields_cons[local]:
  !st bs name tv fs dst mem.
    storage_live_fields st bs ((name,tv)::fs) dst mem ==>
    storage_live_memory st bs tv dst mem /\
    storage_live_fields st (bs + type_slot_size tv) fs
      (dst + 32 * type_slot_size tv) mem
Proof
  rpt gen_tac >>
  rewrite_tac[storage_live_fields_def, storage_live_memory_def,
    type_slot_size_def] >>
  `dead_bytes_fields st bs ((name,tv)::fs) =
     (\j b. dead_bytes st bs tv j b \/
       dead_bytes_fields st (bs + type_slot_size tv) fs j b)` by
    simp[FUN_EQ_THM, dead_bytes_def] >>
  pop_assum SUBST1_TAC >> strip_tac >> irule copy_bytes_split >> simp[] >>
  conj_tac >> rpt strip_tac
  >- (drule (cj 1 dead_bytes_range) >> simp[]) >>
  drule (cj 3 dead_bytes_range) >> simp[]
QED

Theorem storage_live_memory_tuple:
  !st bs tvs dst mem.
    storage_live_memory st bs (TupleTV tvs) dst mem <=>
    storage_live_list st bs tvs dst mem
Proof
  simp[storage_live_memory_def, storage_live_list_def,
       type_slot_size_def, copy_bytes_def, dead_bytes_def]
QED

Theorem storage_live_memory_struct:
  !st bs fs dst mem.
    storage_live_memory st bs (StructTV fs) dst mem <=>
    storage_live_fields st bs fs dst mem
Proof
  simp[storage_live_memory_def, storage_live_fields_def,
       type_slot_size_def, copy_bytes_def, dead_bytes_def]
QED

Theorem slot_block_index[local]:
  !sz i k off.
    off < sz /\ k * sz <= i * sz + off /\
    i * sz + off < (k + 1) * sz ==> k = i
Proof
  rpt strip_tac >>
  `0 < sz` by decide_tac >>
  `((i * sz + off) DIV sz) = i` by
    (irule arithmeticTheory.DIV_UNIQUE >> qexists_tac `off` >> simp[]) >>
  `((i * sz + off) DIV sz) = k` by
    (irule arithmeticTheory.DIV_UNIQUE >>
     qexists_tac `i * sz + off - k * sz` >>
     simp[] >> decide_tac) >>
  gvs[]
QED

Theorem storage_live_memory_fixed_element:
  !st bs tv n dst mem i.
    storage_live_memory st bs (ArrayTV tv (Fixed n)) dst mem /\ i < n ==>
    storage_live_memory st (bs + i * type_slot_size tv) tv
      (dst + 32 * (i * type_slot_size tv)) mem
Proof
  rpt gen_tac >>
  rewrite_tac[storage_live_memory_def, type_slot_size_def] >> strip_tac >>
  irule copy_bytes_subregion >>
  qexistsl [`dead_bytes st bs (ArrayTV tv (Fixed n))`,
            `n * type_slot_size tv`] >> simp[] >> reverse conj_tac
  >- (`(i + 1) * type_slot_size tv <= n * type_slot_size tv` by
        simp[] >>
      qpat_x_assum `(i + 1) * _ <= _` mp_tac >>
      pure_rewrite_tac[arithmeticTheory.RIGHT_ADD_DISTRIB,
        arithmeticTheory.MULT_RIGHT_1] >> decide_tac) >>
  rpt strip_tac >> gvs[dead_bytes_def] >>
  rename1 `k < n` >>
  drule (cj 1 dead_bytes_range) >> strip_tac >>
  `k = i` by
    (irule slot_block_index >> qexistsl [`i'`, `type_slot_size tv`] >>
     simp[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >>
  gvs[]
QED

Theorem storage_live_memory_dynamic_element:
  !st bs tv n dst mem i.
    storage_live_memory st bs (ArrayTV tv (Dynamic n)) dst mem /\
    i < n /\ i < w2n (lookup_storage (n2w bs) st) ==>
    storage_live_memory st (bs + (1 + i * type_slot_size tv)) tv
      (dst + 32 * (1 + i * type_slot_size tv)) mem
Proof
  rpt gen_tac >>
  rewrite_tac[storage_live_memory_def, type_slot_size_def] >> strip_tac >>
  irule copy_bytes_subregion >>
  qexistsl [`dead_bytes st bs (ArrayTV tv (Dynamic n))`,
            `1 + n * type_slot_size tv`] >> simp[] >> reverse conj_tac
  >- (`(i + 1) * type_slot_size tv <= n * type_slot_size tv` by simp[] >>
      qpat_x_assum `(i + 1) * _ <= _` mp_tac >>
      pure_rewrite_tac[arithmeticTheory.RIGHT_ADD_DISTRIB,
        arithmeticTheory.MULT_RIGHT_1] >> decide_tac) >>
  rpt strip_tac >> gvs[dead_bytes_def] >> rename1 `k < n` >>
  Cases_on `k < w2n (lookup_storage (n2w bs) st)`
  >- (gvs[] >> drule (cj 1 dead_bytes_range) >> strip_tac >>
      `k = i` by
        (irule slot_block_index >> qexistsl [`i'`, `type_slot_size tv`] >>
         simp[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >> gvs[]) >>
  gvs[] >>
  `k = i` by
    (irule slot_block_index >> qexistsl [`i'`, `type_slot_size tv`] >>
     simp[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >> gvs[]
QED

(* A repeated sequence exposes the observations of each child, not dead
   capacity after the used prefix. *)
Definition storage_live_elements_def:
  storage_live_elements st bs tv n dst mem <=>
    !i. i < n ==>
      storage_live_memory st (bs + i * type_slot_size tv) tv
        (dst + 32 * (i * type_slot_size tv)) mem
End

Theorem storage_live_elements_cons[local]:
  !st bs tv n dst mem.
    storage_live_elements st bs tv (SUC n) dst mem <=>
    storage_live_memory st bs tv dst mem /\
    storage_live_elements st (bs + type_slot_size tv) tv n
      (dst + 32 * type_slot_size tv) mem
Proof
  rpt gen_tac >> rewrite_tac[storage_live_elements_def] >> eq_tac
  >- (strip_tac >> conj_tac
      >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >>
      pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES,
        arithmeticTheory.LEFT_ADD_DISTRIB, arithmeticTheory.ADD_ASSOC] >> simp[]) >>
  strip_tac >> qx_gen_tac `i` >> Cases_on `i`
  >- simp[] >>
  pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES,
    arithmeticTheory.LEFT_ADD_DISTRIB, arithmeticTheory.ADD_ASSOC,
    arithmeticTheory.LESS_MONO_EQ] >> strip_tac >>
  first_x_assum drule >> pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >>
  simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem storage_live_fixed_elements[local]:
  !st bs tv n dst mem.
    storage_live_memory st bs (ArrayTV tv (Fixed n)) dst mem ==>
    storage_live_elements st bs tv n dst mem
Proof
  simp[storage_live_elements_def] >> rpt strip_tac >>
  drule_all storage_live_memory_fixed_element >> simp[]
QED

Theorem storage_live_dynamic_elements[local]:
  !st bs tv n len dst mem.
    storage_live_memory st bs (ArrayTV tv (Dynamic n)) dst mem /\
    len = w2n (lookup_storage (n2w bs) st) /\ len <= n ==>
    storage_live_elements st (bs + 1) tv len (dst + 32) mem
Proof
  simp[storage_live_elements_def] >> rpt strip_tac >>
  drule storage_live_memory_dynamic_element >>
  disch_then (qspec_then `i` mp_tac) >>
  `i < n` by decide_tac >>
  pure_rewrite_tac[arithmeticTheory.LEFT_ADD_DISTRIB,
    arithmeticTheory.MULT_RIGHT_1] >>
  asm_simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem canonical_primitive_in_memory:
  !tv w dst mem.
    well_formed_type_value tv /\ word_slot_canonical w tv /\
    mem_word_at dst mem = w /\
    ((?bt. tv = BaseTV bt /\ (!n. bt <> BytesT (Dynamic n)) /\
                              (!n. bt <> StringT n)) \/
     (?m. tv = FlagTV m)) ==>
    val_in_memory tv (decode_base_from_slot w tv) dst mem
Proof
  rpt gen_tac >> strip_tac >>
  `encode_base_to_slot (decode_base_from_slot w tv) tv = SOME w` by
    gvs[word_slot_canonical_def] >>
  gvs[]
  >- (Cases_on `bt` >>
      gvs[decode_base_from_slot_def, encode_base_to_slot_def,
          val_in_memory_def, val_to_w256_def, typed_val_to_w256_def,
          bool_to_slot_def, AllCaseEqs()] >>
      Cases_on `b` >>
      gvs[decode_base_from_slot_def, encode_base_to_slot_def,
          val_in_memory_def, typed_val_to_w256_def,
          valueEncodingProofsTheory.word_of_bytes_be_pad_right,
          AllCaseEqs()])
  >> gvs[decode_base_from_slot_def, encode_base_to_slot_def,
         val_in_memory_def, val_to_w256_def]
QED

Theorem none_decode_in_memory:
  !w dst mem. val_in_memory NoneTV (decode_base_from_slot w NoneTV) dst mem
Proof
  simp[decode_base_from_slot_def, val_in_memory_def]
QED

Theorem slots_to_bytes_take[local]:
  !slots n. slots_to_bytes n slots =
    TAKE n (FLAT (MAP (\w. word_to_bytes (w:bytes32) T) slots))
Proof
  Induct >> simp[slots_to_bytes_def] >>
  gen_tac >> Cases_on `n` >>
  simp[slots_to_bytes_def, byteTheory.word_to_bytes_be_def,
       TAKE_APPEND, byteTheory.LENGTH_word_to_bytes, LENGTH_TAKE_EQ,
       arithmeticTheory.MIN_DEF] >>
  IF_CASES_TAC >>
  simp[byteTheory.LENGTH_word_to_bytes, TAKE_LENGTH_TOO_LONG]
QED

Theorem read_slots_length[local]:
  !n st bs. LENGTH (read_slots st bs n) = n
Proof
  Induct >> simp[read_slots_def]
QED

Theorem read_slots_index[local]:
  !n st bs i. i < n ==>
    EL i (read_slots st bs n) = read_slot st (bs + i)
Proof
  Induct >> simp[read_slots_def] >>
  rpt gen_tac >> Cases_on `i`
  >- simp[read_slot_def] >>
  simp[] >> strip_tac >>
  pure_rewrite_tac[arithmeticTheory.ADD1] >>
  simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem flat_word_bytes_length[local]:
  !ws. LENGTH (FLAT (MAP (\w. word_to_bytes (w:bytes32) T) ws)) =
       32 * LENGTH ws
Proof
  Induct >> simp[byteTheory.LENGTH_word_to_bytes]
QED

Theorem flat_word_bytes_index[local]:
  !ws k. k < 32 * LENGTH ws ==>
    EL k (FLAT (MAP (\w. word_to_bytes (w:bytes32) T) ws)) =
    EL (k MOD 32) (word_to_bytes (EL (k DIV 32) ws) T)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `k < 32`
  >- simp[EL_APPEND1, byteTheory.LENGTH_word_to_bytes,
          arithmeticTheory.LESS_DIV_EQ_ZERO, arithmeticTheory.LESS_MOD] >>
  `?j. k = 32 + j` by (qexists `k - 32` >> decide_tac) >>
  gvs[EL_APPEND2, byteTheory.LENGTH_word_to_bytes,
      arithmeticTheory.ADD_DIV_ADD_DIV, arithmeticTheory.ADD_MOD,
      arithmeticTheory.MULT_CLAUSES] >>
  `(j + 32) DIV 32 = SUC (j DIV 32)` by
    (`j + 32 = 1 * 32 + j` by simp[] >>
     pop_assum SUBST1_TAC >> simp[arithmeticTheory.ADD_DIV_ADD_DIV]) >>
  asm_rewrite_tac[EL, TL]
QED

Theorem decode_dyn_bytes_observations:
  !st bs max vs.
    decode_dyn_bytes st bs max = SOME vs ==>
    LENGTH vs = w2n (read_slot st bs) /\ LENGTH vs <= max /\
    (!k. k < LENGTH vs ==>
      EL k vs = EL (k MOD 32)
        (word_to_bytes (read_slot st (bs + 1 + k DIV 32)) T))
Proof
  simp[decode_dyn_bytes_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[GSYM read_slot_def, slots_to_bytes_take] >>
  `w2n (read_slot st bs) <=
     LENGTH (FLAT (MAP (\w. word_to_bytes (w:bytes32) T)
       (read_slots st (bs + 1) (word_size (w2n (read_slot st bs))))))` by
    simp[flat_word_bytes_length, read_slots_length, word_size_capacity] >>
  gvs[LENGTH_TAKE_EQ] >>
  simp[EL_TAKE] >>
  `k < 32 * word_size (w2n (read_slot st bs))` by
    (mp_tac (Q.SPEC `w2n (read_slot st bs)` word_size_capacity) >> decide_tac) >>
  simp[flat_word_bytes_index, read_slots_length] >>
  `k DIV 32 < word_size (w2n (read_slot st bs))` by
    simp[arithmeticTheory.DIV_LT_X] >>
  simp[read_slots_index] >>
  pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >>
  simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem copy_dyn_bytes_contents[local]:
  !st bs max dst mem vs.
    copy_bytes st bs (1 + word_size max) (dyn_bytes_dead st bs max) dst mem /\
    decode_dyn_bytes st bs max = SOME vs ==>
    mem_word_at dst mem = n2w (LENGTH vs) /\
    mem_bytes_at (dst + 32) (LENGTH vs) mem = vs
Proof
  rpt strip_tac >>
  drule decode_dyn_bytes_observations >> strip_tac
  >- (irule copy_bytes_word >> rpt strip_tac >>
      qpat_x_assum `copy_bytes _ _ _ _ _ _` mp_tac >>
      simp[copy_bytes_def] >>
      disch_then (qspecl_then [`0`, `b`] mp_tac) >>
      simp[dyn_bytes_dead_def]) >>
  irule LIST_EQ >> simp[valueEncodingProofsTheory.LENGTH_mem_bytes_at_proof] >>
  qx_gen_tac `k` >> strip_tac >>
  `k DIV 32 < word_size max` by
    (simp[arithmeticTheory.DIV_LT_X] >>
     mp_tac (Q.SPEC `max` word_size_capacity) >> decide_tac) >>
  `k MOD 32 < 32` by simp[] >>
  `k = 32 * (k DIV 32) + k MOD 32` by
    (qspec_then `32` mp_tac arithmeticTheory.DIVISION >>
     simp[] >> disch_then (qspec_then `k` mp_tac) >> decide_tac) >>
  qpat_x_assum `copy_bytes _ _ _ _ _ _` mp_tac >>
  simp[copy_bytes_def] >>
  disch_then (qspecl_then [`1 + k DIV 32`, `k MOD 32`] mp_tac) >>
  simp[dyn_bytes_dead_def, GSYM read_slot_def] >>
  strip_tac >>
  `dst + 32 * (k DIV 32 + 1) + k MOD 32 = dst + 32 + k` by decide_tac >>
  gvs[valueEncodingProofsTheory.EL_mem_bytes_at]
QED

Theorem dynamic_bytes_decode_in_memory:
  !st bs max dst mem vs.
    storage_live_memory st bs (BaseTV (BytesT (Dynamic max))) dst mem /\
    decode_dyn_bytes st bs max = SOME vs ==>
    val_in_memory (BaseTV (BytesT (Dynamic max))) (BytesV vs) dst mem
Proof
  `!st bs max. dead_bytes st bs (BaseTV (BytesT (Dynamic max))) =
                dyn_bytes_dead st bs max` by
    simp[FUN_EQ_THM, dead_bytes_def] >>
  simp[storage_live_memory_def, type_slot_size_def, val_in_memory_def] >>
  metis_tac[copy_dyn_bytes_contents, arithmeticTheory.ADD_COMM]
QED

Theorem bytes_string_roundtrip[local]:
  !bs:byte list. MAP (n2w o ORD) (MAP (CHR o w2n) bs) = bs
Proof
  Induct >> simp[] >> gen_tac >>
  `w2n (h:byte) < 256` by
    (mp_tac (Q.ISPEC `h:byte` wordsTheory.w2n_lt) >>
     simp[wordsTheory.dimword_8]) >>
  simp[stringTheory.ORD_CHR]
QED

Theorem string_decode_in_memory:
  !st bs max dst mem vs.
    storage_live_memory st bs (BaseTV (StringT max)) dst mem /\
    decode_dyn_bytes st bs max = SOME vs ==>
    val_in_memory (BaseTV (StringT max))
      (StringV (MAP (CHR o w2n) vs)) dst mem
Proof
  `!st bs max. dead_bytes st bs (BaseTV (StringT max)) =
                dyn_bytes_dead st bs max` by
    simp[FUN_EQ_THM, dead_bytes_def] >>
  simp[storage_live_memory_def, type_slot_size_def,
       val_in_memory_def, bytes_string_roundtrip] >>
  metis_tac[copy_dyn_bytes_contents, arithmeticTheory.ADD_COMM]
QED

Theorem decode_live_memory_mutual[local]:
  (!st bs tv. !v dst mem.
    well_formed_type_value tv /\ slots_in_range st bs tv /\
    decode_value st bs tv = SOME v /\ storage_live_memory st bs tv dst mem ==>
    val_in_memory tv v dst mem) /\
  (!st bs tvs. !vs dst mem.
    EVERY well_formed_type_value tvs /\ tuple_slots_in_range st bs tvs /\
    decode_tuple st bs tvs = SOME vs /\ storage_live_list st bs tvs dst mem ==>
    tuple_in_memory vs tvs dst mem) /\
  (!st bs tv n. !vs dst mem.
    well_formed_type_value tv /\ static_slots_in_range st bs tv n /\
    decode_static_array st bs tv n = SOME vs /\
    storage_live_elements st bs tv n dst mem ==>
    LENGTH vs = n /\ elems_in_memory vs dst tv mem) /\
  (!st bs tv n. !vs dst mem.
    well_formed_type_value tv /\ dyn_slots_in_range st bs tv n /\
    decode_dyn_array st bs tv n = SOME vs /\
    storage_live_elements st bs tv n dst mem ==>
    LENGTH vs = n /\ elems_in_memory vs dst tv mem) /\
  (!st bs fs. !vs dst mem.
    EVERY (\p. well_formed_type_value (SND p)) fs /\
    struct_slots_in_range st bs fs /\ decode_struct st bs fs = SOME vs /\
    storage_live_fields st bs fs dst mem ==>
    fields_in_memory vs fs dst mem)
Proof
  ho_match_mp_tac decode_value_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[Once decode_value_def, AllCaseEqs()] >>
      irule dynamic_bytes_decode_in_memory >> metis_tac[])
  >- (rpt strip_tac >> gvs[Once decode_value_def, AllCaseEqs()] >>
      irule string_decode_in_memory >> metis_tac[])
  >- (rpt strip_tac >> gvs[Once decode_value_def, slots_in_range_def] >>
      irule canonical_primitive_in_memory >> simp[] >>
      irule storage_live_memory_head >> goal_assum (drule_at Any) >> simp[type_slot_size_def])
  >- (rpt strip_tac >> gvs[Once decode_value_def, slots_in_range_def] >>
      irule canonical_primitive_in_memory >> simp[] >>
      irule storage_live_memory_head >> goal_assum (drule_at Any) >> simp[type_slot_size_def])
  >- (rpt strip_tac >> gvs[Once decode_value_def, slots_in_range_def] >>
      irule canonical_primitive_in_memory >> simp[] >>
      irule storage_live_memory_head >> goal_assum (drule_at Any) >> simp[type_slot_size_def])
  >- (rpt strip_tac >> gvs[Once decode_value_def, slots_in_range_def] >>
      irule canonical_primitive_in_memory >> simp[] >>
      irule storage_live_memory_head >> goal_assum (drule_at Any) >> simp[type_slot_size_def])
  >- (rpt strip_tac >> gvs[Once decode_value_def, slots_in_range_def] >>
      irule canonical_primitive_in_memory >> simp[] >>
      irule storage_live_memory_head >> goal_assum (drule_at Any) >> simp[type_slot_size_def])
  >- (rpt strip_tac >> gvs[Once decode_value_def, slots_in_range_def] >>
      irule canonical_primitive_in_memory >> simp[] >>
      irule storage_live_memory_head >> goal_assum (drule_at Any) >> simp[type_slot_size_def])
  >- (rpt strip_tac >> gvs[Once decode_value_def, slots_in_range_def] >>
      irule canonical_primitive_in_memory >> simp[] >>
      irule storage_live_memory_head >> goal_assum (drule_at Any) >> simp[type_slot_size_def])
  >- simp[Once decode_value_def, val_in_memory_def]
  >- (rpt strip_tac >>
      gvs[Once decode_value_def, AllCaseEqs(), val_in_memory_def,
          well_formed_type_value_def, slots_in_range_def, storage_live_memory_tuple] >>
      first_x_assum irule >> fs[ETA_THM, combinTheory.o_DEF])
  >- (rpt strip_tac >>
      gvs[Once decode_value_def, AllCaseEqs(), slots_in_range_def,
          well_formed_type_value_def] >>
      drule storage_live_fixed_elements >> strip_tac >>
      first_x_assum (drule_then strip_assume_tac) >>
      irule (REWRITE_RULE[make_array_value_def] fixed_array_from_dense) >> simp[])
  >- (rpt strip_tac >>
      gvs[Once decode_value_def, AllCaseEqs(), slots_in_range_def,
          well_formed_type_value_def] >>
      `storage_live_elements st (bs + 1) tv (w2n (read_slot st bs))
          (dst + 32) mem` by
        (irule storage_live_dynamic_elements >> simp[read_slot_def] >>
         qexists_tac `max` >> fs[read_slot_def]) >>
      `MIN (w2n (read_slot st bs)) max = w2n (read_slot st bs)` by
        (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
      gvs[] >> first_x_assum (drule_then strip_assume_tac) >>
      simp[val_in_memory_def] >> irule storage_live_memory_head >>
      goal_assum (drule_at Any) >> simp[type_slot_size_def])
  >- (rpt strip_tac >>
      gvs[Once decode_value_def, AllCaseEqs(), val_in_memory_def,
          well_formed_type_value_def, slots_in_range_def, storage_live_memory_struct] >>
      first_x_assum irule >> fs[ETA_THM, combinTheory.o_DEF])
  >- simp[decode_value_def, val_in_memory_def]
  >- (rpt strip_tac >>
      gvs[Once decode_value_def, AllCaseEqs(), slots_in_range_def] >>
      drule storage_live_list_cons >> strip_tac >>
      simp[val_in_memory_def, type_memory_size_slots])
  >- simp[decode_value_def, val_in_memory_def]
  >- (rpt strip_tac >>
      gvs[Once decode_value_def, AllCaseEqs(), slots_in_range_def,
          storage_live_elements_cons] >>
      first_x_assum (drule_then strip_assume_tac) >>
      first_x_assum (drule_then strip_assume_tac) >>
      simp[val_in_memory_def, type_memory_size_slots])
  >- simp[decode_value_def, val_in_memory_def]
  >- (rpt strip_tac >>
      gvs[Once decode_value_def, AllCaseEqs(), slots_in_range_def,
          storage_live_elements_cons] >>
      first_x_assum (drule_then strip_assume_tac) >>
      first_x_assum (drule_then strip_assume_tac) >>
      simp[val_in_memory_def, type_memory_size_slots])
  >- simp[decode_value_def, val_in_memory_def]
  >> rpt strip_tac >>
  gvs[Once decode_value_def, AllCaseEqs(), slots_in_range_def] >>
  drule storage_live_fields_cons >> strip_tac >>
  simp[val_in_memory_def, type_memory_size_slots]
QED

Theorem decode_value_live_memory:
  !st bs tv v dst mem.
    well_formed_type_value tv /\ slots_in_range st bs tv /\
    decode_value st bs tv = SOME v /\ storage_live_memory st bs tv dst mem ==>
    val_in_memory tv v dst mem
Proof
  metis_tac[decode_live_memory_mutual]
QED

Theorem copied_storage_live_memory:
  !cx tr st rt w tv dst mem.
    storage_read_live cx tr st w tv /\
    storage_agree (storage_dead cx tr st) st rt /\
    (!i. i < type_slot_size tv ==>
      mem_word_at (dst + 32 * i) mem = lookup_storage (w + n2w i) rt) ==>
    storage_live_memory st (w2n w) tv dst mem
Proof
  rpt gen_tac >> strip_tac >>
  simp[storage_live_memory_def, copy_bytes_def] >> rpt strip_tac >>
  `~storage_dead cx tr st (w2n (w + n2w i)) b` by
    (strip_tac >>
     qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[storage_read_live_def] >>
     disch_then drule >> strip_tac >>
     `w2n w + i < dimword (:256)` by decide_tac >>
     `w2n (w + n2w i) = w2n w + i` by
       (Cases_on `w` >> fs[wordsTheory.word_add_n2w]) >>
     gvs[] >> first_x_assum irule >> decide_tac) >>
  qpat_x_assum `!i. i < _ ==> _` drule >> strip_tac >>
  simp[valueEncodingProofsTheory.mem_bytes_at_word] >>
  qpat_x_assum `storage_agree _ _ _` mp_tac >>
  simp[storage_agree_def] >>
  disch_then (qspecl_then [`w + n2w i`, `b`] mp_tac) >>
  simp[read_slot_def] >>
  Cases_on `w` >> fs[wordsTheory.word_add_n2w, arithmeticTheory.ADD_COMM]
QED

Theorem copied_storage_decode_in_memory:
  !cx tr st rt w tv v dst mem.
    well_formed_type_value tv /\ slots_in_range st (w2n w) tv /\
    decode_value st (w2n w) tv = SOME v /\
    storage_read_live cx tr st w tv /\
    storage_agree (storage_dead cx tr st) st rt /\
    (!i. i < type_slot_size tv ==>
      mem_word_at (dst + 32 * i) mem = lookup_storage (w + n2w i) rt) ==>
    val_in_memory tv v dst mem
Proof
  rpt strip_tac >> irule decode_value_live_memory >> simp[] >>
  qexistsl_tac [`w2n w`, `st`] >> simp[] >>
  irule copied_storage_live_memory >>
  qexistsl_tac [`cx`, `rt`, `tr`] >> simp[]
QED
