(* Typed storage transport for deferred argument forcing. *)
Theory bodyIntCallStorageLayout
Ancestors
  compileEnv vyperEncodeDecode vyperLookupStorage words accountsRelProps
  vyperStorage byte list venomMemProps valueEncoding valueEncodingProps valueTypingMemoryProps abiDecoderString abiDecoderFixedMemory exprSimAttributeFields

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

Theorem decode_storage_live_agree:
  (!st off tv st'.
    (!j b. off <= j /\ j < off + type_slot_size tv /\ b < 32 /\
      ~dead_bytes st off tv j b ==>
      EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
      EL b (word_to_bytes (lookup_storage (n2w j) st') T)) ==>
    decode_value st' off tv = decode_value st off tv) /\
  (!st off tvs st'.
    (!j b. off <= j /\ j < off + type_slot_size_list tvs /\ b < 32 /\
      ~dead_bytes_list st off tvs j b ==>
      EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
      EL b (word_to_bytes (lookup_storage (n2w j) st') T)) ==>
    decode_tuple st' off tvs = decode_tuple st off tvs) /\
  (!st off tv n st'.
    (!i. i < n ==> !j b.
      off+i*type_slot_size tv <= j /\
      j < off+i*type_slot_size tv+type_slot_size tv /\ b < 32 /\
      ~dead_bytes st (off+i*type_slot_size tv) tv j b ==>
      EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
      EL b (word_to_bytes (lookup_storage (n2w j) st') T)) ==>
    decode_static_array st' off tv n = decode_static_array st off tv n) /\
  (!st off tv n st'.
    (!i. i < n ==> !j b.
      off+i*type_slot_size tv <= j /\
      j < off+i*type_slot_size tv+type_slot_size tv /\ b < 32 /\
      ~dead_bytes st (off+i*type_slot_size tv) tv j b ==>
      EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
      EL b (word_to_bytes (lookup_storage (n2w j) st') T)) ==>
    decode_dyn_array st' off tv n = decode_dyn_array st off tv n) /\
  (!st off fields st'.
    (!j b. off <= j /\ j < off + type_slot_size_fields fields /\ b < 32 /\
      ~dead_bytes_fields st off fields j b ==>
      EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
      EL b (word_to_bytes (lookup_storage (n2w j) st') T)) ==>
    decode_struct st' off fields = decode_struct st off fields)
Proof
  ho_match_mp_tac decode_value_ind >> rpt conj_tac >> rpt gen_tac >>
  strip_tac
  >~ [`decode_value st' off (BaseTV (BytesT (Dynamic max)))`]
  >- (`decode_dyn_bytes st' off max = decode_dyn_bytes st off max` by
       (irule decode_dyn_bytes_live_agree >> rpt strip_tac >>
        first_x_assum irule >>
        gvs[vyperValueTheory.type_slot_size_def, dead_bytes_def]) >>
     simp[decode_value_def])
  >~ [`decode_value st' off (BaseTV (StringT max))`]
  >- (`decode_dyn_bytes st' off max = decode_dyn_bytes st off max` by
       (irule decode_dyn_bytes_live_agree >> rpt strip_tac >>
        first_x_assum irule >>
        gvs[vyperValueTheory.type_slot_size_def, dead_bytes_def]) >>
     simp[decode_value_def])
  >> simp[decode_value_def, read_slot_def]
  >>~- ([`decode_base_from_slot`],
    qmatch_asmsub_abbrev_tac `type_slot_size ty` >>
    `lookup_storage (n2w off) st' = lookup_storage (n2w off) st` by
      (irule storage_live_value_head >> qexists `ty` >>
       simp[Abbr `ty`, vyperValueTheory.type_slot_size_def]) >> simp[])
  >> rpt strip_tac
  >~ [`type_slot_size (TupleTV _)`]
  >- (gvs[vyperValueTheory.type_slot_size_def, dead_bytes_def] >>
      first_x_assum drule >> simp[])
  >~ [`type_slot_size (StructTV _)`]
  >- (gvs[vyperValueTheory.type_slot_size_def, dead_bytes_def] >>
      first_x_assum drule >> simp[])
  >~ [`type_slot_size (ArrayTV _ (Fixed _))`]
  >- (`decode_static_array st' off tv n = decode_static_array st off tv n` by
        (first_x_assum irule >> metis_tac[storage_live_fixed_element]) >> simp[])
  >~ [`type_slot_size (ArrayTV _ (Dynamic _))`]
  >- suspend "dynamic_array"
  >~ [`type_slot_size_list (_::_)`]
  >- suspend "tuple_cons"
  >~ [`type_slot_size_fields (_::_)`]
  >- (`decode_value st' off tv = decode_value st off tv` by
        (qpat_x_assum `!st'. _ ==> decode_value _ _ _ = _` irule >>
         metis_tac[storage_live_fields_head]) >> simp[] >>
      Cases_on `decode_value st off tv` >> simp[] >>
      gvs[] >> qpat_x_assum `!st'. _ ==> decode_struct _ _ _ = _`
        (qspec_then `st'` mp_tac) >>
      (impl_tac >- (drule storage_live_fields_tail >> simp[])) >> simp[])
  >> qpat_assum `!i. i < SUC n ==> _` (qspec_then `0` mp_tac) >>
  simp[] >> disch_tac >>
  `decode_value st' off tv = decode_value st off tv` by
    (qpat_x_assum `!st'. _ ==> decode_value _ _ _ = _` irule >> simp[]) >>
  simp[] >> Cases_on `decode_value st off tv` >> simp[] >> gvs[] >>
  qpat_x_assum `!st'. (!i. i < n ==> _) ==> _`
    (qspec_then `st'` mp_tac) >>
  (impl_tac >-
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `!i. i < SUC n ==> _` (qspec_then `SUC i` mp_tac) >>
     simp[arithmeticTheory.MULT_CLAUSES])) >> simp[]
QED

Resume decode_storage_live_agree[dynamic_array]:
  `lookup_storage (n2w off) st' = lookup_storage (n2w off) st` by
    (irule storage_live_value_head >>
     qexists `ArrayTV tv (Dynamic max)` >>
     simp[vyperValueTheory.type_slot_size_def]) >> simp[] >>
  Cases_on `w2n (lookup_storage (n2w off) st) <= max` >> simp[] >>
  `decode_dyn_array st' (off+1) tv (MIN (w2n (lookup_storage (n2w off) st)) max) =
   decode_dyn_array st (off+1) tv (MIN (w2n (lookup_storage (n2w off) st)) max)` by
    (first_x_assum irule >> simp[read_slot_def] >> rpt strip_tac >>
     `i < max /\ i < w2n (lookup_storage (n2w off) st)` by decide_tac >>
     irule storage_live_dynamic_element >> simp[] >>
     qexistsl [`max`, `i`, `off`, `tv`] >> simp[]) >> simp[]
QED

Resume decode_storage_live_agree[tuple_cons]:
  `decode_value st' off tv = decode_value st off tv` by
    (qpat_x_assum `!st'. _ ==> decode_value _ _ _ = _` irule >>
     metis_tac[storage_live_tuple_head]) >> simp[] >>
  Cases_on `decode_value st off tv` >> simp[] >>
  gvs[] >> qpat_x_assum `!st'. _ ==> decode_tuple _ _ _ = _`
    (qspec_then `st'` mp_tac) >>
  (impl_tac >- (drule storage_live_tuple_tail >> simp[])) >> simp[]
QED

Finalise decode_storage_live_agree

Theorem slots_storage_live_agree:
  (!st off tv st'.
    (!j b. off <= j /\ j < off + type_slot_size tv /\ b < 32 /\
      ~dead_bytes st off tv j b ==>
      EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
      EL b (word_to_bytes (lookup_storage (n2w j) st') T)) ==>
    (slots_in_range st' off tv <=> slots_in_range st off tv)) /\
  (!st off tvs st'.
    (!j b. off <= j /\ j < off + type_slot_size_list tvs /\ b < 32 /\
      ~dead_bytes_list st off tvs j b ==>
      EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
      EL b (word_to_bytes (lookup_storage (n2w j) st') T)) ==>
    (tuple_slots_in_range st' off tvs <=> tuple_slots_in_range st off tvs)) /\
  (!st off tv n st'.
    (!i. i < n ==> !j b.
      off+i*type_slot_size tv <= j /\
      j < off+i*type_slot_size tv+type_slot_size tv /\ b < 32 /\
      ~dead_bytes st (off+i*type_slot_size tv) tv j b ==>
      EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
      EL b (word_to_bytes (lookup_storage (n2w j) st') T)) ==>
    (static_slots_in_range st' off tv n <=> static_slots_in_range st off tv n)) /\
  (!st off tv n st'.
    (!i. i < n ==> !j b.
      off+i*type_slot_size tv <= j /\
      j < off+i*type_slot_size tv+type_slot_size tv /\ b < 32 /\
      ~dead_bytes st (off+i*type_slot_size tv) tv j b ==>
      EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
      EL b (word_to_bytes (lookup_storage (n2w j) st') T)) ==>
    (dyn_slots_in_range st' off tv n <=> dyn_slots_in_range st off tv n)) /\
  (!st off fields st'.
    (!j b. off <= j /\ j < off + type_slot_size_fields fields /\ b < 32 /\
      ~dead_bytes_fields st off fields j b ==>
      EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
      EL b (word_to_bytes (lookup_storage (n2w j) st') T)) ==>
    (struct_slots_in_range st' off fields <=> struct_slots_in_range st off fields))
Proof
  ho_match_mp_tac slots_in_range_ind >> rpt conj_tac >> rpt gen_tac >>
  strip_tac
  >>~- ([`type_slot_size (BaseTV _)`],
    qmatch_asmsub_abbrev_tac `type_slot_size ty` >>
    `lookup_storage (n2w off) st' = lookup_storage (n2w off) st` by
      (irule storage_live_value_head >> qexists `ty` >>
       simp[Abbr `ty`, vyperValueTheory.type_slot_size_def]) >>
    simp[Abbr `ty`, slots_in_range_def, read_slot_def])
  >~ [`type_slot_size (FlagTV _)`]
  >- (qmatch_asmsub_abbrev_tac `type_slot_size ty` >>
      `lookup_storage (n2w off) st' = lookup_storage (n2w off) st` by
        (irule storage_live_value_head >> qexists `ty` >>
         simp[Abbr `ty`, vyperValueTheory.type_slot_size_def]) >>
      simp[Abbr `ty`, slots_in_range_def, read_slot_def])
  >> simp[slots_in_range_def, read_slot_def] >> rpt strip_tac
  >~ [`type_slot_size (TupleTV _)`]
  >- (gvs[vyperValueTheory.type_slot_size_def, dead_bytes_def] >>
      first_x_assum irule >> simp[])
  >~ [`type_slot_size (StructTV _)`]
  >- (gvs[vyperValueTheory.type_slot_size_def, dead_bytes_def] >>
      first_x_assum irule >> simp[])
  >~ [`type_slot_size (ArrayTV _ (Fixed _))`]
  >- (first_x_assum irule >> metis_tac[storage_live_fixed_element])
  >~ [`type_slot_size (ArrayTV _ (Dynamic _))`]
  >- (`lookup_storage (n2w off) st' = lookup_storage (n2w off) st` by
        (irule storage_live_value_head >>
         qexists `ArrayTV tv (Dynamic max)` >>
         simp[vyperValueTheory.type_slot_size_def]) >> simp[] >>
      Cases_on `w2n (lookup_storage (n2w off) st) <= max` >> simp[] >>
      first_x_assum irule >> simp[read_slot_def] >> rpt strip_tac >>
      `i < max /\ i < w2n (lookup_storage (n2w off) st)` by decide_tac >>
      irule storage_live_dynamic_element >> simp[] >>
      qexistsl [`max`, `i`, `off`, `tv`] >> simp[])
  >~ [`type_slot_size_list (_::_)`]
  >- (drule storage_live_tuple_head >> disch_tac >>
      drule storage_live_tuple_tail >> disch_tac >> gvs[] >> metis_tac[])
  >~ [`type_slot_size_fields (_::_)`]
  >- (drule storage_live_fields_head >> disch_tac >>
      drule storage_live_fields_tail >> disch_tac >> gvs[] >> metis_tac[])
  >> qpat_assum `!i. i < SUC n ==> _` (qspec_then `0` mp_tac) >>
  simp[] >> disch_tac >>
  `(slots_in_range st' off tv <=> slots_in_range st off tv)` by
    (qpat_x_assum `!st'. _ ==> (slots_in_range _ _ _ <=> _)` irule >> simp[]) >>
  simp[] >> qpat_x_assum `!st'. (!i. i < n ==> _) ==> _`
    (qspec_then `st'` mp_tac) >>
  (impl_tac >-
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `!i. i < SUC n ==> _` (qspec_then `SUC i` mp_tac) >>
     simp[arithmeticTheory.MULT_CLAUSES])) >> simp[]
QED

Theorem decode_value_storage_live_agree:
  !st st' off tv.
    (!j b. off <= j /\ j < off + type_slot_size tv /\ b < 32 /\
      ~dead_bytes st off tv j b ==>
      EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
      EL b (word_to_bytes (lookup_storage (n2w j) st') T)) ==>
    decode_value st' off tv = decode_value st off tv
Proof
  metis_tac[cj 1 decode_storage_live_agree]
QED

Theorem slots_in_range_storage_live_agree:
  !st st' off tv.
    (!j b. off <= j /\ j < off + type_slot_size tv /\ b < 32 /\
      ~dead_bytes st off tv j b ==>
      EL b (word_to_bytes (lookup_storage (n2w j) st) T) =
      EL b (word_to_bytes (lookup_storage (n2w j) st') T)) ==>
    (slots_in_range st' off tv <=> slots_in_range st off tv)
Proof
  metis_tac[cj 1 slots_storage_live_agree]
QED

Theorem decode_value_storage_read_live:
  !cx tr st st' a tv.
    storage_agree (storage_dead cx tr st) st st' /\
    storage_read_live cx tr st a tv ==>
    decode_value st' (w2n a) tv = decode_value st (w2n a) tv
Proof
  rpt strip_tac >> irule decode_value_storage_live_agree >>
  metis_tac[storage_read_live_window]
QED

Theorem slots_in_range_storage_read_live:
  !cx tr st st' a tv.
    storage_agree (storage_dead cx tr st) st st' /\
    storage_read_live cx tr st a tv ==>
    (slots_in_range st' (w2n a) tv <=> slots_in_range st (w2n a) tv)
Proof
  rpt strip_tac >> irule slots_in_range_storage_live_agree >>
  metis_tac[storage_read_live_window]
QED

(* Canonicality is conditional on type well-formedness. *)
Theorem decoded_scalar_in_memory:
  !st off tv v b mem.
    well_formed_type_value tv /\
    word_slot_canonical (read_slot st off) tv /\
    decode_base_from_slot (read_slot st off) tv = v /\
    mem_word_at b mem = read_slot st off ==>
    val_in_memory tv v b mem
Proof
  rpt gen_tac >> strip_tac >>
  `encode_base_to_slot v tv = SOME (read_slot st off)` by
    gvs[word_slot_canonical_def] >>
  Cases_on `v` >> Cases_on `tv` >>
  gvs[encode_base_to_slot_def, val_in_memory_def, val_to_w256_def,
      typed_val_to_w256_def, AllCaseEqs()] >>
  rename1 `encode_base_to_slot _ (BaseTV bt) = SOME _` >>
  Cases_on `bt` >>
  gvs[encode_base_to_slot_def, decode_base_from_slot_def,
      typed_val_to_w256_def, bool_to_slot_def, AllCaseEqs()] >>
  rename1 `BaseTV (BytesT bd)` >> Cases_on `bd` >>
  gvs[encode_base_to_slot_def, decode_base_from_slot_def,
      vyperTypingTheory.well_formed_type_value_def] >>
  simp[valueEncodingProofsTheory.word_of_bytes_be_pad_right]
QED

Theorem mem_bytes_at_word_prefix:
  !b len mem. len <= 32 ==>
    mem_bytes_at b len mem = TAKE len (word_to_bytes_be (mem_word_at b mem))
Proof
  rpt strip_tac >>
  rewrite_tac[word_to_bytes_be_def, GSYM valueEncodingProofsTheory.mem_bytes_at_word] >>
  irule LIST_EQ >> simp[LENGTH_mem_bytes_at, LENGTH_TAKE_EQ] >>
  rpt strip_tac >> simp[EL_TAKE, valueEncodingProofsTheory.EL_mem_bytes_at]
QED

(* Exact copied words determine any prefix of the payload window. *)
Theorem copied_slots_bytes:
  !n st off b mem len.
    len <= 32*n /\
    (!j. j < n ==> mem_word_at (b+32*j) mem = read_slot st (off+j)) ==>
    mem_bytes_at b len mem = slots_to_bytes len (read_slots st off n)
Proof
  Induct >- simp[slots_to_bytes_def, mem_bytes_at_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `len`
  >- simp[mem_bytes_at_def, slots_to_bytes_def] >>
  `mem_word_at b mem = read_slot st off` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  rename1 `SUC len <= 32 * SUC n` >>
  Cases_on `SUC len <= 32`
  >- (simp[read_slots_def, slots_to_bytes_def, arithmeticTheory.MIN_DEF,
           mem_bytes_at_word_prefix, GSYM read_slot_def]) >>
  `mem_bytes_at b (SUC len) mem =
   mem_bytes_at b 32 mem ++ mem_bytes_at (b+32) (SUC len-32) mem` by
    (qspecl_then [`b`, `32`, `SUC len-32`, `mem`] mp_tac
       valueEncodingProofsTheory.mem_bytes_at_split_padded >> simp[]) >>
  simp[read_slots_def, slots_to_bytes_def, arithmeticTheory.MIN_DEF,
       GSYM read_slot_def] >>
  simp[valueEncodingProofsTheory.mem_bytes_at_word, word_to_bytes_be_def,
       LENGTH_word_to_bytes, dimindex_256, TAKE_LENGTH_TOO_LONG] >>
  first_x_assum irule >> conj_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then `SUC j` mp_tac) >>
      `b + 32 * SUC j = b+32+32*j` by decide_tac >>
      `off + SUC j = off+1+j` by decide_tac >> simp[]) >>
  decide_tac
QED

Theorem decoded_dynamic_bytes_memory:
  !st off max bs b mem.
    decode_dyn_bytes st off max = SOME bs /\
    (!j. j < 1 + word_size max ==>
      mem_word_at (b+32*j) mem = read_slot st (off+j)) ==>
    mem_word_at b mem = n2w (LENGTH bs) /\
    mem_bytes_at (b+32) (LENGTH bs) mem = bs
Proof
  rpt gen_tac >> strip_tac >>
  gvs[decode_dyn_bytes_def, AllCaseEqs()] >>
  qmatch_goalsub_abbrev_tac `slots_to_bytes len (read_slots st (off+1) (word_size len))` >>
  `word_size len <= word_size max` by
    (simp[vfmConstantsTheory.word_size_def] >>
     irule arithmeticTheory.DIV_LE_MONOTONE >> simp[Abbr `len`]) >>
  `mem_bytes_at (b+32) len mem =
   slots_to_bytes len (read_slots st (off+1) (word_size len))` by
    (irule copied_slots_bytes >> conj_tac
     >- (rpt strip_tac >> first_x_assum (qspec_then `SUC j` mp_tac) >>
         `b+32*SUC j = b+32+32*j` by decide_tac >>
         `SUC j+off = off+1+j` by decide_tac >> simp[]) >>
     simp[word_size_capacity]) >>
  `LENGTH (slots_to_bytes len (read_slots st (off+1) (word_size len))) = len` by
    metis_tac[LENGTH_mem_bytes_at] >>
  simp[] >> first_x_assum (qspec_then `0` mp_tac) >>
  simp[Abbr `len`, read_slot_def]
QED

Theorem decoded_base_in_memory:
  !st off bt v b mem.
    well_formed_type_value (BaseTV bt) /\
    slots_in_range st off (BaseTV bt) /\
    decode_value st off (BaseTV bt) = SOME v /\
    (!j. j < type_slot_size (BaseTV bt) ==>
      mem_word_at (b+32*j) mem = read_slot st (off+j)) ==>
    val_in_memory (BaseTV bt) v b mem
Proof
  rpt gen_tac >> strip_tac >> Cases_on `bt` >>
  gvs[decode_value_def, slots_in_range_def, AllCaseEqs()]
  >~ [`decode_dyn_bytes _ _ _ = SOME _`]
  >- (gvs[vyperValueTheory.type_slot_size_def] >>
      drule decoded_dynamic_bytes_memory >>
      disch_then (qspecl_then [`b`, `mem`] mp_tac) >>
      simp[] >> strip_tac >>
      simp[val_in_memory_def, abi_decoder_string_bytes_roundtrip])
  >~ [`BaseTV (BytesT _)`]
  >- (rename1 `BaseTV (BytesT bd)` >> Cases_on `bd` >>
      gvs[decode_value_def, slots_in_range_def, AllCaseEqs()]
      >~ [`decode_dyn_bytes`]
      >- (gvs[vyperValueTheory.type_slot_size_def] >>
          drule decoded_dynamic_bytes_memory >>
          disch_then (qspecl_then [`b`, `mem`] mp_tac) >>
          simp[val_in_memory_def]) >>
      irule decoded_scalar_in_memory >> simp[] >>
      goal_assum (drule_at Any) >>
      gvs[vyperValueTheory.type_slot_size_def]) >>
  irule decoded_scalar_in_memory >> simp[] >>
  goal_assum (drule_at Any) >>
  gvs[vyperValueTheory.type_slot_size_def]
QED

Theorem copied_slot_subwindow:
  !st off b mem n k m.
    (!j. j < n ==> mem_word_at (b+32*j) mem = read_slot st (off+j)) /\
    k+m <= n ==>
    !j. j < m ==>
      mem_word_at (b+32*k+32*j) mem = read_slot st (off+k+j)
Proof
  rpt strip_tac >> first_x_assum (qspec_then `k+j` mp_tac) >>
  `k+j < n` by decide_tac >>
  `b+32*(k+j) = b+32*k+32*j` by decide_tac >>
  `off+(k+j) = off+k+j` by decide_tac >> simp[]
QED

Theorem decoded_copied_memory_mutual:
  (!st off tv v b mem.
    decode_value st off tv = SOME v ==>
    well_formed_type_value tv /\ slots_in_range st off tv /\
    (!j. j < type_slot_size tv ==>
      mem_word_at (b+32*j) mem = read_slot st (off+j)) ==>
    val_in_memory tv v b mem) /\
  (!st off tvs vs b mem.
    decode_tuple st off tvs = SOME vs ==>
    EVERY well_formed_type_value tvs /\ tuple_slots_in_range st off tvs /\
    (!j. j < type_slot_size_list tvs ==>
      mem_word_at (b+32*j) mem = read_slot st (off+j)) ==>
    tuple_in_memory vs tvs b mem) /\
  (!st off tv n vs b mem.
    decode_static_array st off tv n = SOME vs ==>
    well_formed_type_value tv /\ static_slots_in_range st off tv n /\
    (!j. j < n*type_slot_size tv ==>
      mem_word_at (b+32*j) mem = read_slot st (off+j)) ==>
    LENGTH vs = n /\ elems_in_memory vs b tv mem) /\
  (!st off tv n vs b mem.
    decode_dyn_array st off tv n = SOME vs ==>
    well_formed_type_value tv /\ dyn_slots_in_range st off tv n /\
    (!j. j < n*type_slot_size tv ==>
      mem_word_at (b+32*j) mem = read_slot st (off+j)) ==>
    LENGTH vs = n /\ elems_in_memory vs b tv mem) /\
  (!st off fields vs b mem.
    decode_struct st off fields = SOME vs ==>
    EVERY (well_formed_type_value o SND) fields /\
    struct_slots_in_range st off fields /\
    (!j. j < type_slot_size_fields fields ==>
      mem_word_at (b+32*j) mem = read_slot st (off+j)) ==>
    fields_in_memory vs fields b mem)
Proof
  ho_match_mp_tac decode_value_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac
  >>~- ([`val_in_memory (BaseTV _)`], irule decoded_base_in_memory >> metis_tac[])
  >~ [`val_in_memory (FlagTV _)`]
  >- (gvs[decode_value_def, slots_in_range_def] >>
      irule decoded_scalar_in_memory >> simp[] >>
      goal_assum (drule_at Any) >> gvs[vyperValueTheory.type_slot_size_def])
  >~ [`val_in_memory NoneTV`]
  >- gvs[decode_value_def, val_in_memory_def] >>
  gvs[decode_value_def, slots_in_range_def, val_in_memory_def,
      vyperTypingTheory.well_formed_type_value_def, AllCaseEqs()]
  >~ [`type_slot_size (TupleTV _)`]
  >- (gvs[vyperValueTheory.type_slot_size_def, ETA_THM] >> first_x_assum irule >> simp[])
  >~ [`type_slot_size (StructTV _)`]
  >- (gvs[vyperValueTheory.type_slot_size_def, ETA_THM] >> first_x_assum irule >> simp[])
  >~ [`type_slot_size (ArrayTV _ (Fixed _))`]
  >- (gvs[vyperValueTheory.type_slot_size_def] >>
      `LENGTH vs = n /\ elems_in_memory vs b tv mem` by
        (first_x_assum irule >> simp[]) >>
      irule (SRULE [val_in_memory_def] abi_decoder_fixed_array_memory) >>
      qpat_x_assum `LENGTH vs = n` (SUBST_ALL_TAC o SYM) >>
      simp[tuple_in_memory_replicate])
  >~ [`type_slot_size (ArrayTV _ (Dynamic _))`]
  >- suspend "dynamic_array"
  >~ [`tuple_in_memory _ _ _ _`]
  >- suspend "tuple_cons" >>
  gvs[vyperValueTheory.type_slot_size_def, type_memory_size_slots,
      arithmeticTheory.MULT_CLAUSES]
  >~ [`fields_in_memory _ _ _ _`]
  >- (first_x_assum irule >> rpt strip_tac >>
      first_x_assum (qspec_then `type_slot_size tv + j` mp_tac) >>
      `b + 32 * (type_slot_size tv + j) = b + 32 * type_slot_size tv + 32 * j` by decide_tac >>
      `type_slot_size tv + j + off = j + (off + type_slot_size tv)` by decide_tac >> simp[]) >>
  `LENGTH vs' = n /\ elems_in_memory vs' (b + 32 * type_slot_size tv) tv mem` by
    (first_x_assum irule >> rpt strip_tac >>
     first_x_assum (qspec_then `type_slot_size tv + j` mp_tac) >>
     `b + 32 * (type_slot_size tv + j) = b + 32 * type_slot_size tv + 32 * j` by decide_tac >>
     `type_slot_size tv + j + off = j + (off + type_slot_size tv)` by decide_tac >> simp[]) >>
  simp[]
QED

Resume decoded_copied_memory_mutual[tuple_cons]:
  gvs[vyperValueTheory.type_slot_size_def, type_memory_size_slots] >>
  first_x_assum irule >> rpt strip_tac >>
  first_x_assum (qspec_then `type_slot_size tv + j` mp_tac) >>
  `b + 32 * (type_slot_size tv + j) = b + 32 * type_slot_size tv + 32 * j` by decide_tac >>
  `type_slot_size tv + j + off = j + (off + type_slot_size tv)` by decide_tac >>
  simp[]
QED


Resume decoded_copied_memory_mutual[dynamic_array]:
  `MIN (w2n (read_slot st off)) max = w2n (read_slot st off)` by
    simp[arithmeticTheory.MIN_DEF] >>
  gvs[vyperValueTheory.type_slot_size_def] >>
  `LENGTH vs = w2n (read_slot st off) /\ elems_in_memory vs (b+32) tv mem` by
    (first_x_assum irule >> rpt strip_tac >>
     first_x_assum (qspec_then `SUC j` mp_tac) >>
     `SUC j < type_slot_size tv * max + 1` by
       (`type_slot_size tv * w2n (read_slot st off) <= type_slot_size tv * max` by
          simp[arithmeticTheory.LE_MULT_LCANCEL] >> decide_tac) >>
     `b+32*SUC j = b+32+32*j` by decide_tac >>
     `SUC j+off = j+(off+1)` by decide_tac >> simp[]) >>
  simp[] >> first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Finalise decoded_copied_memory_mutual


Theorem decoded_copied_in_memory:
  !st off tv v b mem.
    well_formed_type_value tv /\ slots_in_range st off tv /\
    decode_value st off tv = SOME v /\
    (!j. j < type_slot_size tv ==>
      mem_word_at (b+32*j) mem = read_slot st (off+j)) ==>
    val_in_memory tv v b mem
Proof
  metis_tac[cj 1 decoded_copied_memory_mutual]
QED

(* Agreement is needed only on live bytes. In particular no equality of
   the dead suffix of the last payload slot is assumed. *)
Theorem storage_read_copied_in_memory:
  !cx tr st st' a tv v b mem.
    storage_agree (storage_dead cx tr st) st st' /\
    storage_read_live cx tr st a tv /\
    well_formed_type_value tv /\ slots_in_range st (w2n a) tv /\
    decode_value st (w2n a) tv = SOME v /\
    (!j. j < type_slot_size tv ==>
      mem_word_at (b+32*j) mem = read_slot st' (w2n a+j)) ==>
    val_in_memory tv v b mem
Proof
  rpt gen_tac >> strip_tac >>
  drule_all decode_value_storage_read_live >> strip_tac >>
  drule_all slots_in_range_storage_read_live >> strip_tac >>
  irule decoded_copied_in_memory >> simp[] >> qexistsl [`w2n a`, `st'`] >> simp[]
QED
