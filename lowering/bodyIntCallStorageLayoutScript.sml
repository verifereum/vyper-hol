(* Typed storage transport for deferred argument forcing. *)
Theory bodyIntCallStorageLayout
Ancestors
  compileEnv vyperEncodeDecode vyperLookupStorage words accountsRelProps
  vyperStorage byte list venomMemProps

(* Selected reads inherit agreement at their live bytes, including when
   slot arithmetic is modular. A globally dead byte forces this particular
   read to fit the natural slot interval, by storage_read_live. *)
Theorem storage_read_live_byte_agreement:
  !cx tr st st' a tv i b.
    storage_agree (storage_dead cx tr st) st st' /\
    storage_read_live cx tr st a tv /\ i < type_slot_size tv /\ b < 32 /\
    ~dead_bytes st (w2n a) tv (w2n a+i) b ==>
    EL b (word_to_bytes (lookup_storage (n2w (w2n a+i)) st) T) =
    EL b (word_to_bytes (lookup_storage (n2w (w2n a+i)) st') T)
Proof
  rpt gen_tac >> strip_tac >>
  `~storage_dead cx tr st (w2n (n2w (w2n a+i) : bytes32)) b` by
    (strip_tac >>
     qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[storage_read_live_def] >>
     disch_then drule >> strip_tac >>
     `w2n a+i < dimword (:256)` by decide_tac >>
     gvs[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  gvs[storage_agree_def]
QED

(* Only the requested prefix of each payload word is observed. *)
Theorem slots_to_bytes_read_live_prefix:
  !n st st' off len.
    (!i b. i < n /\ b < 32 /\ 32*i+b < len ==>
      EL b (word_to_bytes (lookup_storage (n2w (off+i)) st) T) =
      EL b (word_to_bytes (lookup_storage (n2w (off+i)) st') T)) ==>
    slots_to_bytes len (read_slots st off n) =
    slots_to_bytes len (read_slots st' off n)
Proof
  Induct >- simp[read_slots_def, slots_to_bytes_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `len`
  >- gvs[slots_to_bytes_def] >>
  rename1 `SUC len` >>
  simp[read_slots_def, slots_to_bytes_def] >>
  `TAKE (MIN 32 (SUC len)) (word_to_bytes_be (lookup_storage (n2w off) st)) =
   TAKE (MIN 32 (SUC len)) (word_to_bytes_be (lookup_storage (n2w off) st'))` by
     (irule LIST_EQ >>
      simp[word_to_bytes_be_def, LENGTH_TAKE_EQ, LENGTH_word_to_bytes, dimindex_256] >>
      rpt strip_tac >> gvs[LENGTH_TAKE_EQ, LENGTH_word_to_bytes, dimindex_256] >>
      simp[EL_TAKE] >>
      first_x_assum (qspecl_then [`0`, `x`] mp_tac) >> simp[]) >>
  simp[] >> first_x_assum irule >> rpt strip_tac >>
  first_x_assum (qspecl_then [`SUC i`, `b`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  (impl_tac >- (gvs[arithmeticTheory.MIN_DEF, arithmeticTheory.MULT_CLAUSES] >>
                decide_tac)) >>
  `i + (off + 1) = SUC (i + off)` by decide_tac >> simp[]
QED

Theorem decode_dyn_bytes_live_agree:
  !st st' off max.
    (!i b. i < 1 + word_size max /\ b < 32 /\
       ~dyn_bytes_dead st off max (off+i) b ==>
       EL b (word_to_bytes (lookup_storage (n2w (off+i)) st) T) =
       EL b (word_to_bytes (lookup_storage (n2w (off+i)) st') T)) ==>
    decode_dyn_bytes st' off max = decode_dyn_bytes st off max
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_storage (n2w off) st = lookup_storage (n2w off) st'` by
    (irule word_to_bytes_EL_eq >> rpt strip_tac >>
     first_x_assum (qspecl_then [`0`, `b`] mp_tac) >>
     simp[dyn_bytes_dead_def]) >>
  simp[decode_dyn_bytes_def] >>
  Cases_on `w2n (lookup_storage (n2w off) st') <= max` >> simp[] >>
  sym_tac >> irule slots_to_bytes_read_live_prefix >>
  rpt strip_tac >>
  `word_size (w2n (lookup_storage (n2w off) st')) <= word_size max` by
    (simp[vfmConstantsTheory.word_size_def] >>
     irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]) >>
  first_x_assum (qspecl_then [`i+1`, `b`] mp_tac) >>
  simp[dyn_bytes_dead_def] >>
  (impl_tac >- (rpt conj_tac >> decide_tac)) >>
  `off + (i+1) = off+1+i` by decide_tac >> simp[]
QED

Theorem storage_live_tuple_head:
  !st st' off tv tvs.
    (!j b. off <= j /\ j < off + type_slot_size_list (tv::tvs) /\
       b < 32 /\ ~dead_bytes_list st off (tv::tvs) j b ==>
       EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
       EL b (word_to_bytes (lookup_storage (n2w j) st') T)) ==>
    (!j b. off <= j /\ j < off + type_slot_size tv /\
       b < 32 /\ ~dead_bytes st off tv j b ==>
       EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
       EL b (word_to_bytes (lookup_storage (n2w j) st') T))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> simp[vyperValueTheory.type_slot_size_def, dead_bytes_def] >>
  strip_tac >> drule (cj 2 dead_bytes_range) >> decide_tac
QED

Theorem storage_live_tuple_tail:
  !st st' off tv tvs.
    (!j b. off <= j /\ j < off + type_slot_size_list (tv::tvs) /\
       b < 32 /\ ~dead_bytes_list st off (tv::tvs) j b ==>
       EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
       EL b (word_to_bytes (lookup_storage (n2w j) st') T)) ==>
    (!j b. off + type_slot_size tv <= j /\
       j < off + type_slot_size tv + type_slot_size_list tvs /\
       b < 32 /\ ~dead_bytes_list st (off + type_slot_size tv) tvs j b ==>
       EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
       EL b (word_to_bytes (lookup_storage (n2w j) st') T))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> simp[vyperValueTheory.type_slot_size_def, dead_bytes_def] >>
  strip_tac >> drule (cj 1 dead_bytes_range) >> decide_tac
QED

Theorem storage_live_fields_head:
  !st st' off name tv fields.
    (!j b. off <= j /\ j < off + type_slot_size_fields ((name,tv)::fields) /\
       b < 32 /\ ~dead_bytes_fields st off ((name,tv)::fields) j b ==>
       EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
       EL b (word_to_bytes (lookup_storage (n2w j) st') T)) ==>
    (!j b. off <= j /\ j < off + type_slot_size tv /\
       b < 32 /\ ~dead_bytes st off tv j b ==>
       EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
       EL b (word_to_bytes (lookup_storage (n2w j) st') T))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> simp[vyperValueTheory.type_slot_size_def, dead_bytes_def] >>
  strip_tac >> drule (cj 3 dead_bytes_range) >> decide_tac
QED

Theorem storage_live_fields_tail:
  !st st' off name tv fields.
    (!j b. off <= j /\ j < off + type_slot_size_fields ((name,tv)::fields) /\
       b < 32 /\ ~dead_bytes_fields st off ((name,tv)::fields) j b ==>
       EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
       EL b (word_to_bytes (lookup_storage (n2w j) st') T)) ==>
    (!j b. off + type_slot_size tv <= j /\
       j < off + type_slot_size tv + type_slot_size_fields fields /\
       b < 32 /\ ~dead_bytes_fields st (off + type_slot_size tv) fields j b ==>
       EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
       EL b (word_to_bytes (lookup_storage (n2w j) st') T))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> simp[vyperValueTheory.type_slot_size_def, dead_bytes_def] >>
  strip_tac >> drule (cj 1 dead_bytes_range) >> decide_tac
QED

(* Disjointness of equal-width element windows, also for zero width. *)
Theorem array_slot_window_index:
  !off s i k j.
    off + i*s <= j /\ j < off + (i+1)*s /\
    off + k*s <= j /\ j < off + (k+1)*s ==> i = k
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `i < k`
  >- (`(i+1)*s <= k*s` by
        (irule arithmeticTheory.LESS_MONO_MULT2 >> decide_tac) >> decide_tac) >>
  Cases_on `k < i`
  >- (`(k+1)*s <= i*s` by
        (irule arithmeticTheory.LESS_MONO_MULT2 >> decide_tac) >> decide_tac) >>
  decide_tac
QED

Theorem array_slot_window_bound[local]:
  !i n s off. i < n ==> off + i*s+s <= off+n*s
Proof
  rpt strip_tac >>
  `(i+1)*s <= n*s` by
    (irule arithmeticTheory.LESS_MONO_MULT2 >> decide_tac) >>
  qpat_x_assum `(i+1)*s <= n*s` mp_tac >>
  pure_rewrite_tac[arithmeticTheory.RIGHT_ADD_DISTRIB,
                   arithmeticTheory.MULT_LEFT_1] >> decide_tac
QED

Theorem storage_live_fixed_element:
  !st st' off tv n i.
    (!j b. off <= j /\ j < off + type_slot_size (ArrayTV tv (Fixed n)) /\
       b < 32 /\ ~dead_bytes st off (ArrayTV tv (Fixed n)) j b ==>
       EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
       EL b (word_to_bytes (lookup_storage (n2w j) st') T)) /\ i < n ==>
    (!j b. off + i*type_slot_size tv <= j /\
       j < off + i*type_slot_size tv + type_slot_size tv /\
       b < 32 /\ ~dead_bytes st (off + i*type_slot_size tv) tv j b ==>
       EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
       EL b (word_to_bytes (lookup_storage (n2w j) st') T))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `i < n` (mp_tac o MATCH_MP array_slot_window_bound) >>
  disch_then (qspecl_then [`type_slot_size tv`, `off`] assume_tac) >>
  first_x_assum irule >> simp[vyperValueTheory.type_slot_size_def] >>
  pure_rewrite_tac[dead_bytes_def] >> strip_tac >>
  rename1 `dead_bytes st (off + k*type_slot_size tv) tv j b` >>
  drule (cj 1 dead_bytes_range) >> strip_tac >>
  `i = k` by
    (irule array_slot_window_index >> qexistsl [`j`, `off`, `type_slot_size tv`] >>
     simp[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >> gvs[]
QED

Theorem storage_live_value_head:
  !st st' off tv.
    (!j b. off <= j /\ j < off + type_slot_size tv /\
       b < 32 /\ ~dead_bytes st off tv j b ==>
       EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
       EL b (word_to_bytes (lookup_storage (n2w j) st') T)) /\
    0 < type_slot_size tv ==>
    lookup_storage (n2w off) st' = lookup_storage (n2w off) st
Proof
  rpt gen_tac >> strip_tac >> sym_tac >> irule word_to_bytes_EL_eq >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  strip_tac >> drule (cj 1 dead_bytes_range) >> simp[]
QED

Theorem storage_live_dynamic_element:
  !st st' off tv cap i.
    (!j b. off <= j /\ j < off + type_slot_size (ArrayTV tv (Dynamic cap)) /\
       b < 32 /\ ~dead_bytes st off (ArrayTV tv (Dynamic cap)) j b ==>
       EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
       EL b (word_to_bytes (lookup_storage (n2w j) st') T)) /\
    i < cap /\ i < w2n (lookup_storage (n2w off) st) ==>
    (!j b. off+1 + i*type_slot_size tv <= j /\
       j < off+1 + i*type_slot_size tv + type_slot_size tv /\
       b < 32 /\ ~dead_bytes st (off+1 + i*type_slot_size tv) tv j b ==>
       EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
       EL b (word_to_bytes (lookup_storage (n2w j) st') T))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `i < cap` (mp_tac o MATCH_MP array_slot_window_bound) >>
  disch_then (qspecl_then [`type_slot_size tv`, `off+1`] assume_tac) >>
  first_x_assum irule >> simp[vyperValueTheory.type_slot_size_def] >>
  pure_rewrite_tac[dead_bytes_def] >> strip_tac >>
  rename1 `k < cap` >>
  Cases_on `k < w2n (lookup_storage (n2w off) st)`
  >- (gvs[] >> drule (cj 1 dead_bytes_range) >> strip_tac >>
      `i = k` by
        (irule array_slot_window_index >>
         qexistsl [`j`, `off+1`, `type_slot_size tv`] >>
         simp[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >> gvs[]) >>
  gvs[] >>
  `i = k` by
    (irule array_slot_window_index >>
     qexistsl [`j`, `off+1`, `type_slot_size tv`] >>
     simp[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >> gvs[]
QED

Theorem indexed_slot_windows_cons:
  !P off s n.
    (!i. i < SUC n ==> P (off+i*s)) ==>
    P off /\ (!i. i < n ==> P (off+s+i*s))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >>
  `off + SUC i * s = off+s+i*s` by
    (pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >> simp[]
QED

Theorem storage_read_live_window:
  !cx tr st st' a tv.
    storage_agree (storage_dead cx tr st) st st' /\
    storage_read_live cx tr st a tv ==>
    (!j b. w2n a <= j /\ j < w2n a + type_slot_size tv /\
       b < 32 /\ ~dead_bytes st (w2n a) tv j b ==>
       EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
       EL b (word_to_bytes (lookup_storage (n2w j) st') T))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule storage_read_live_byte_agreement >>
  disch_then (qspecl_then [`a`, `tv`, `j-w2n a`, `b`] mp_tac) >> simp[]
QED
