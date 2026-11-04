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
