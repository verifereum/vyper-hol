(* Byte observations for storage values copied to memory. *)
Theory storageDecodeMemory
Ancestors
  list rich_list words valueEncoding valueEncodingProps compileEnv
  vyperLookupStorage vyperStorage vyperValue accountsRelProps venomMemProps

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
    (first_x_assum irule >> simp[]) >>
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
