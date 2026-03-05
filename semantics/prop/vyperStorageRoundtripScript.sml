(*
 * vyperStorageRoundtripScript.sml
 *
 * Storage encode/decode roundtrip properties.
 *
 * TOP-LEVEL:
 *   roundtrip_ok_def - predicate: type/value pair round-trips through storage
 *   roundtrip_all - all well-formed values round-trip
 *)

Theory vyperStorageRoundtrip
Ancestors
  vyperTyping vyperStorage vyperValue vfmState byte list rich_list combin bitstring
  bit sorting arithmetic pair indexedLists vfmConstants
Libs
  wordsLib dep_rewrite

(* ===== Roundtrip Predicate ===== *)

Definition roundtrip_ok_def:
  roundtrip_ok tv v ⇔
    ∀writes base storage.
      encode_value tv v = SOME writes ⇒
      decode_value (apply_writes (n2w base) writes storage) base tv = SOME v
End

(* ===== Byte Roundtrip ===== *)

Theorem LENGTH_word_to_bytes_be_256[local]:
  LENGTH (word_to_bytes_be (w : bytes32)) = 32
Proof
  simp[word_to_bytes_be_def, LENGTH_word_to_bytes]
QED

Theorem word_to_bytes_be_word_of_bytes_be[local]:
  LENGTH (xs : word8 list) = 32 ⇒
  word_to_bytes_be (word_of_bytes_be xs : bytes32) = xs
Proof
  strip_tac >>
  simp[LIST_EQ_REWRITE,
       word_to_bytes_be_def, word_of_bytes_be_def,
       LENGTH_word_to_bytes, word_to_bytes_def,
       EL_word_to_bytes_aux,
       get_byte_word_of_bytes_be,
       first_byte_at_0w]
QED

Theorem word_of_bytes_be_word_to_bytes_be[local]:
  word_of_bytes_be (word_to_bytes_be (w : bytes32)) = w
Proof
  simp[word_to_bytes_be_def, word_of_bytes_be_def,
       word_of_bytes_word_to_bytes]
QED

(* ===== apply_writes Properties ===== *)

Theorem apply_writes_nil[local]:
  apply_writes base [] storage = storage
Proof
  simp[apply_writes_def]
QED

Theorem read_slot_after_apply_writes_single[local]:
  read_slot (apply_writes (n2w base) [(0, val0)] storage) base = val0
Proof
  simp[read_slot_def, apply_writes_def, lookup_storage_def, update_storage_def,
       APPLY_UPDATE_THM]
QED

Theorem apply_writes_append[local]:
  ∀ws1 ws2 base storage.
    apply_writes base (ws1 ++ ws2) storage =
    apply_writes base ws2 (apply_writes base ws1 storage)
Proof
  Induct >> simp[apply_writes_def] >>
  Cases >> simp[apply_writes_def]
QED

Theorem n2w_add_mod_l[local]:
  n2w (a MOD dimword(:256) + b) = n2w (a + b) : bytes32
Proof
  simp[wordsTheory.n2w_11, bitTheory.MOD_PLUS_RIGHT, arithmeticTheory.MOD_PLUS]
QED

Theorem n2w_add_rearrange[local]:
  n2w (a + (b + c MOD dimword(:256))) = n2w (b + (a + c) MOD dimword(:256)) : bytes32
Proof
  simp[wordsTheory.n2w_11, arithmeticTheory.MOD_PLUS, bitTheory.MOD_PLUS_RIGHT]
QED

Theorem apply_writes_shift[local]:
  ∀writes k base storage.
    apply_writes (n2w base) (MAP (λ(off,s). (off + k, s)) writes) storage =
    apply_writes (n2w (base + k)) writes storage
Proof
  Induct >- simp[apply_writes_def] >>
  Cases >> rpt gen_tac >>
  simp_tac bool_ss [MAP, apply_writes_def, pairTheory.UNCURRY_DEF, LET_THM] >>
  `n2w (w2n (n2w base : bytes32) + (q + k)) =
   n2w (w2n (n2w (base + k) : bytes32) + q) : bytes32` by
    simp[wordsTheory.n2w_11, arithmeticTheory.MOD_PLUS, bitTheory.MOD_PLUS_RIGHT] >>
  pop_assum SUBST1_TAC >>
  first_x_assum MATCH_ACCEPT_TAC
QED

Theorem apply_writes_lookup_miss[local]:
  ∀writes base storage k.
    (∀off. MEM off (MAP FST writes) ⇒
       n2w (w2n base + off) ≠ (n2w (w2n base + k) : bytes32)) ⇒
    lookup_storage (n2w (w2n base + k))
      (apply_writes base writes storage) =
    lookup_storage (n2w (w2n base + k)) storage
Proof
  Induct >> simp[apply_writes_def] >>
  Cases >> simp[apply_writes_def] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`base`,
    `update_storage (n2w (q + w2n base)) r storage`, `k`] mp_tac) >>
  impl_tac >- (
    rpt strip_tac >> CCONTR_TAC >> gvs[wordsTheory.n2w_11] >>
    first_x_assum (qspec_then `off` mp_tac) >> simp[]
  ) >>
  simp[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM]
QED

Theorem apply_writes_lookup_hit[local]:
  ∀writes base storage k v.
    MEM (k, v) writes ∧
    ALL_DISTINCT (MAP FST writes) ∧
    (∀off. MEM off (MAP FST writes) ∧ off ≠ k ⇒
       n2w (w2n base + off) ≠ (n2w (w2n base + k) : bytes32)) ⇒
    lookup_storage (n2w (w2n base + k)) (apply_writes base writes storage) = v
Proof
  Induct >> simp[apply_writes_def] >>
  Cases >> simp[apply_writes_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  (* gvs resolves the tail-MEM case via IH; remaining: head matches *)
  qspecl_then [`writes`, `base`,
    `update_storage (n2w (k + w2n base)) r storage`, `k`]
    mp_tac apply_writes_lookup_miss >>
  impl_tac >- (
    rpt strip_tac >>
    simp[wordsTheory.n2w_11, arithmeticTheory.MOD_PLUS, bitTheory.MOD_PLUS_RIGHT] >>
    first_x_assum (qspec_then `off` mp_tac) >>
    gvs[wordsTheory.n2w_11, arithmeticTheory.MOD_PLUS, bitTheory.MOD_PLUS_RIGHT] >>
    CCONTR_TAC >> gvs[]
  ) >>
  simp[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM,
       wordsTheory.n2w_11, arithmeticTheory.MOD_PLUS, bitTheory.MOD_PLUS_RIGHT]
QED

(* ===== Bytes/Slots Roundtrip Helpers ===== *)

Theorem bytes_to_slots_aux_acc[local]:
  ∀bs acc. bytes_to_slots_aux acc bs = REVERSE acc ++ bytes_to_slots_aux [] bs
Proof
  measureInduct_on `LENGTH bs` >>
  rpt gen_tac >>
  Cases_on `bs` >- simp[bytes_to_slots_aux_def] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [bytes_to_slots_aux_def])) >>
  CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [bytes_to_slots_aux_def]))) >>
  simp_tac bool_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `bytes_to_slots_aux (w::acc) rest` >>
  `LENGTH rest < SUC (LENGTH t)` by simp[Abbr`rest`] >>
  first_x_assum (qspec_then `rest` mp_tac) >>
  impl_tac >- gvs[] >>
  strip_tac >>
  pop_assum (fn th => REWRITE_TAC [Q.SPEC `w::acc` th, Q.SPEC `[w]` th]) >>
  simp_tac list_ss [REVERSE_DEF]
QED

Theorem slots_to_bytes_bytes_to_slots[local]:
  ∀bs. slots_to_bytes (LENGTH bs) (bytes_to_slots bs) = bs
Proof
  measureInduct_on `LENGTH bs` >>
  Cases_on `bs` >- simp[bytes_to_slots_def, bytes_to_slots_aux_def, slots_to_bytes_def] >>
  (* Step: unfold bytes_to_slots *)
  simp[bytes_to_slots_def] >>
  CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [bytes_to_slots_aux_def]))) >>
  simp_tac bool_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `bytes_to_slots_aux [w] rest` >>
  (* Apply acc lemma *)
  `bytes_to_slots_aux [w] rest = w :: bytes_to_slots_aux [] rest` by (
    qspecl_then [`rest`, `[w]`] mp_tac bytes_to_slots_aux_acc >>
    simp_tac list_ss [REVERSE_DEF, APPEND]
  ) >>
  pop_assum SUBST1_TAC >>
  (* Unfold slots_to_bytes *)
  simp[Once slots_to_bytes_def] >>
  (* word_to_bytes_be w = padded *)
  `word_to_bytes_be w =
    TAKE 32 (h::t) ++ REPLICATE (32 - LENGTH (TAKE 32 (h::t))) 0w` by (
    simp[Abbr`w`] >>
    irule word_to_bytes_be_word_of_bytes_be >>
    simp[LENGTH_APPEND, LENGTH_TAKE_EQ, LENGTH_REPLICATE] >>
    IF_CASES_TAC >> simp[]
  ) >>
  pop_assum SUBST1_TAC >>
  (* TAKE gives back the chunk *)
  `MIN 32 (SUC (LENGTH t)) = LENGTH (TAKE 32 (h::t))` by (
    simp[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >>
    IF_CASES_TAC >> simp[]
  ) >>
  pop_assum (fn th => REWRITE_TAC [th, TAKE_LENGTH_APPEND]) >>
  (* Length of remainder *)
  `SUC (LENGTH t) - LENGTH (TAKE 32 (h::t)) = LENGTH rest` by (
    simp[Abbr`rest`, LENGTH_TAKE_EQ, LENGTH_DROP] >>
    IF_CASES_TAC >> simp[]
  ) >>
  pop_assum SUBST1_TAC >>
  `bytes_to_slots_aux [] rest = bytes_to_slots rest` by simp[bytes_to_slots_def] >>
  pop_assum SUBST1_TAC >>
  `LENGTH rest < LENGTH (h::t)` by simp[Abbr`rest`, LENGTH_DROP] >>
  first_x_assum drule >> strip_tac >>
  simp[Abbr`rest`, TAKE_DROP]
QED

Theorem chr_w2n_n2w_ord[local]:
  ∀s. MAP (CHR o w2n) (MAP ((n2w : num -> word8) o ORD) s) = s
Proof
  Induct >> simp[wordsTheory.w2n_n2w] >>
  gen_tac >>
  `ORD h < 256` by simp[stringTheory.ORD_BOUND] >>
  `dimword(:8) = 256` by EVAL_TAC >>
  gvs[stringTheory.CHR_ORD]
QED

(* ===== Helper: single-slot base type roundtrip ===== *)

(* Helper: for non-dynamic, non-string base types, the roundtrip works
   when encode_base_to_slot succeeds and decode_base_from_slot inverts it *)
Theorem decode_value_single_slot[local]:
  ∀bt v slot.
    (∀nn. bt ≠ BytesT (Dynamic nn)) ∧
    (∀nn. bt ≠ StringT nn) ∧
    encode_base_to_slot v (BaseTV bt) = SOME slot ∧
    decode_base_from_slot slot (BaseTV bt) = v ⇒
    roundtrip_ok (BaseTV bt) v
Proof
  rw[roundtrip_ok_def] >>
  (* encode_value for non-dynamic base types: extract writes = [(0, slot)] *)
  `writes = [(0, slot)]` by (
    Cases_on `bt` >> gvs[]
    >> TRY (rename1 `BytesT bnd` >> Cases_on `bnd` >> gvs[])
    >> fs[decode_base_from_slot_def]
    >> gvs[encode_value_def, AllCaseEqs()]
  ) >> gvs[] >>
  Cases_on `bt` >> gvs[decode_value_def, read_slot_after_apply_writes_single]
  >> rename1 `BytesT bnd` >> Cases_on `bnd`
  >> gvs[decode_value_def, read_slot_after_apply_writes_single]
QED

(* ===== roundtrip_ok: BoolT ===== *)

Theorem slot_to_bool_bool_to_slot[local]:
  ∀b. slot_to_bool (bool_to_slot b) = b
Proof
  Cases >> simp[bool_to_slot_def, slot_to_bool_def]
QED

Theorem roundtrip_ok_bool[local]:
  ∀b. roundtrip_ok (BaseTV BoolT) (BoolV b)
Proof
  rw[] >> irule decode_value_single_slot >> simp[] >>
  qexists_tac `bool_to_slot b` >>
  simp[encode_base_to_slot_def, decode_base_from_slot_def,
       slot_to_bool_bool_to_slot]
QED

(* ===== roundtrip_ok: AddressT ===== *)

Theorem roundtrip_ok_address[local]:
  ∀bs. LENGTH bs = 20 ⇒ roundtrip_ok (BaseTV AddressT) (BytesV (Fixed 20) bs)
Proof
  rw[] >> irule decode_value_single_slot >> simp[] >>
  qexists_tac `word_of_bytes_be (PAD_LEFT 0w 32 bs)` >>
  simp[encode_base_to_slot_def, decode_base_from_slot_def] >>
  DEP_REWRITE_TAC[word_to_bytes_be_word_of_bytes_be] >>
  simp[length_pad_left, PAD_LEFT, DROP_APPEND, LENGTH_GENLIST]
QED

(* ===== roundtrip_ok: BytesT (Fixed n) ===== *)

Theorem roundtrip_ok_fixed_bytes[local]:
  ∀n bs. LENGTH bs = n ∧ n ≤ 32 ⇒
    roundtrip_ok (BaseTV (BytesT (Fixed n))) (BytesV (Fixed n) bs)
Proof
  rw[] >> irule decode_value_single_slot >> simp[] >>
  qexists_tac `word_of_bytes_be (bs ++ REPLICATE (32 - LENGTH bs) 0w)` >>
  simp[encode_base_to_slot_def, decode_base_from_slot_def] >>
  DEP_REWRITE_TAC[word_to_bytes_be_word_of_bytes_be] >>
  simp[LENGTH_APPEND, LENGTH_REPLICATE, TAKE_LENGTH_APPEND]
QED

(* ===== roundtrip_ok: UintT ===== *)

Theorem roundtrip_ok_uint[local]:
  ∀n i. 0 ≤ i ∧ i < &dimword(:256) ⇒
    roundtrip_ok (BaseTV (UintT n)) (IntV (Unsigned n) i)
Proof
  rw[] >> irule decode_value_single_slot >> simp[] >>
  qexists_tac `i2w i` >>
  simp[encode_base_to_slot_def, decode_base_from_slot_def] >>
  simp[integer_wordTheory.w2n_i2w,
       integerTheory.INT_LESS_MOD, integerTheory.INT_OF_NUM]
QED

(* ===== roundtrip_ok: IntT ===== *)

Theorem roundtrip_ok_int[local]:
  ∀n i. INT_MIN(:256) ≤ i ∧ i ≤ INT_MAX(:256) ⇒
    roundtrip_ok (BaseTV (IntT n)) (IntV (Signed n) i)
Proof
  rw[] >> irule decode_value_single_slot >> simp[] >>
  qexists_tac `i2w i` >>
  simp[encode_base_to_slot_def, decode_base_from_slot_def] >>
  simp[integer_wordTheory.w2i_i2w]
QED

(* ===== roundtrip_ok: DecimalT ===== *)

Theorem roundtrip_ok_decimal[local]:
  ∀i. INT_MIN(:256) ≤ i ∧ i ≤ INT_MAX(:256) ⇒
    roundtrip_ok (BaseTV DecimalT) (DecimalV i)
Proof
  rw[] >> irule decode_value_single_slot >> simp[] >>
  qexists_tac `i2w i` >>
  simp[encode_base_to_slot_def, decode_base_from_slot_def] >>
  simp[integer_wordTheory.w2i_i2w]
QED

(* ===== roundtrip_ok: FlagTV ===== *)

Theorem roundtrip_ok_flag[local]:
  ∀m k. k < dimword(:256) ⇒
    roundtrip_ok (FlagTV m) (FlagV m k)
Proof
  rw[roundtrip_ok_def] >>
  gvs[encode_value_def, AllCaseEqs()] >>
  gvs[decode_value_def, read_slot_after_apply_writes_single,
      decode_base_from_slot_def, encode_base_to_slot_def]
QED

(* ===== roundtrip_ok: NoneTV ===== *)

Theorem roundtrip_ok_none[local]:
  roundtrip_ok NoneTV NoneV
Proof
  rw[roundtrip_ok_def, encode_value_def, decode_value_def, apply_writes_nil]
QED

(* ===== Dynamic Bytes/String Roundtrip ===== *)

(* Helper: modular offset cancellation *)
Theorem n2w_add_cancel[local]:
  off < dimword(:256) ∧ k < dimword(:256) ∧ off ≠ k ⇒
  n2w (x + off) ≠ (n2w (x + k) : bytes32)
Proof
  strip_tac >> CCONTR_TAC >> gvs[] >>
  `n2w (x + off) = n2w (x + k) : bytes32` by gvs[] >>
  pop_assum (mp_tac o REWRITE_RULE [GSYM wordsTheory.word_add_n2w]) >>
  simp[wordsTheory.WORD_EQ_ADD_LCANCEL, wordsTheory.n2w_11]
QED

(* Specialization of n2w_add_cancel for k=0 *)
Theorem n2w_add_cancel_0[local]:
  off < dimword(:256) ∧ off ≠ 0 ⇒
  n2w (x + off) ≠ (n2w x : bytes32)
Proof
  strip_tac >>
  `n2w x = n2w (x + 0) : bytes32` by REWRITE_TAC [arithmeticTheory.ADD_0] >>
  pop_assum SUBST1_TAC >>
  irule n2w_add_cancel >> simp[]
QED

(* Helper: n2w (w2n (n2w base) + k) = n2w (base + k) using word algebra.
   wordsLib-safe: avoids simp evaluating w2n to base MOD <huge numeral> *)
Theorem nwn_eq[local]:
  n2w (w2n (n2w base : bytes32) + k) = n2w (base + k) : bytes32
Proof
  REWRITE_TAC [GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n]
QED

(* Numeric-base version of apply_writes_lookup_hit.
   Uses nwn_eq/REWRITE_TAC to avoid wordsLib evaluating dimword(:256) *)
Theorem apply_writes_lookup_hit_num[local]:
  ∀writes base storage k v.
    MEM (k, v) writes ∧
    ALL_DISTINCT (MAP FST writes) ∧
    (∀off. MEM off (MAP FST writes) ∧ off ≠ k ⇒
       n2w (base + off) ≠ (n2w (base + k) : bytes32)) ⇒
    lookup_storage (n2w (base + k))
      (apply_writes (n2w base) writes storage) = v
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC [GSYM nwn_eq] >>
  irule apply_writes_lookup_hit >>
  REWRITE_TAC [nwn_eq] >>
  gvs[]
QED

(* Specialization with k=0: avoids simp simplifying base+0 before irule *)
Theorem apply_writes_lookup_0[local]:
  ∀writes base storage v.
    MEM (0, v) writes ∧
    ALL_DISTINCT (MAP FST writes) ∧
    (∀off. MEM off (MAP FST writes) ∧ off ≠ 0 ⇒
       n2w (base + off) ≠ (n2w base : bytes32)) ⇒
    lookup_storage (n2w base)
      (apply_writes (n2w base) writes storage) = v
Proof
  rpt strip_tac >>
  qspecl_then [`writes`, `base`, `storage`, `0`, `v`]
    mp_tac apply_writes_lookup_hit_num >>
  REWRITE_TAC [arithmeticTheory.ADD_0] >>
  disch_then irule >> gvs[]
QED

(* Helper: read_slots from individual lookups *)
Theorem read_slots_eq_EL[local]:
  ∀n offset storage slots.
    LENGTH slots = n ∧
    (∀i. i < n ⇒
      lookup_storage (n2w (offset + i) : bytes32) storage = EL i slots) ⇒
    read_slots storage offset n = slots
Proof
  Induct >- simp[read_slots_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `slots` >> gvs[read_slots_def] >>
  conj_tac >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  first_x_assum irule >> simp[] >>
  rpt strip_tac >>
  `i + (offset + 1) = offset + SUC i` by DECIDE_TAC >>
  pop_assum SUBST1_TAC >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  simp[]
QED

(* Helper: LENGTH of bytes_to_slots *)
Theorem LENGTH_bytes_to_slots_aux[local]:
  ∀bs acc.
    LENGTH (bytes_to_slots_aux acc bs) =
    LENGTH acc + word_size (LENGTH bs)
Proof
  measureInduct_on `LENGTH bs` >>
  rpt gen_tac >>
  Cases_on `bs` >- simp[bytes_to_slots_aux_def, vfmConstantsTheory.word_size_def] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [bytes_to_slots_aux_def])) >>
  simp_tac bool_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `bytes_to_slots_aux (w::acc) rest` >>
  `LENGTH rest < LENGTH (h::t)` by simp[Abbr`rest`] >>
  first_x_assum drule >> strip_tac >>
  pop_assum (qspec_then `w::acc` mp_tac) >> simp[] >>
  simp[vfmConstantsTheory.word_size_def] >>
  `LENGTH rest = LENGTH t - 31` by
    simp[Abbr`rest`, listTheory.LENGTH_DROP] >>
  simp_tac pure_ss [arithmeticTheory.ADD_CLAUSES] >>
  `SUC (LENGTH t + 31) = 1 * 32 + LENGTH t` by simp[] >>
  pop_assum SUBST1_TAC >>
  simp[arithmeticTheory.ADD_DIV_ADD_DIV] >>
  Cases_on `31 ≤ LENGTH t` >- simp[] >>
  `LENGTH t < 32` by simp[] >>
  simp[arithmeticTheory.LESS_DIV_EQ_ZERO]
QED

Theorem LENGTH_bytes_to_slots[local]:
  LENGTH (bytes_to_slots bs) = word_size (LENGTH bs)
Proof
  simp[bytes_to_slots_def, LENGTH_bytes_to_slots_aux]
QED

(* Helper: MAPi offsets characterization *)
Theorem MEM_MAP_FST_MAPi[local]:
  MEM off (MAP FST (MAPi (λi s. (i + k, s)) slots)) ⇔
  k ≤ off ∧ off < k + LENGTH slots
Proof
  simp[MEM_MAP, indexedListsTheory.MEM_MAPi, pairTheory.EXISTS_PROD] >>
  eq_tac >> rpt strip_tac >> gvs[] >>
  qexists_tac `off - k` >> simp[]
QED

(* Helper: ALL_DISTINCT for consecutive MAPi offsets *)
Theorem ALL_DISTINCT_MAP_FST_MAPi[local]:
  ALL_DISTINCT (MAP FST (MAPi (λi (s:bytes32). (i + k, s)) slots))
Proof
  simp[indexedListsTheory.MAP_MAPi, combinTheory.o_DEF,
       indexedListsTheory.MAPi_GENLIST, listTheory.ALL_DISTINCT_GENLIST]
QED

(* Helper: EL of MAPi *)
Theorem MAPi_EL[local]:
  ∀slots i k.
    i < LENGTH slots ⇒
    MEM (i + k, EL i slots) (MAPi (λj s. (j + k, s)) slots)
Proof
  rpt strip_tac >>
  simp[indexedListsTheory.MEM_MAPi]
QED

(* Bounds compatibility: value bounds match type bounds *)
Definition bounds_compat_def[local]:
  bounds_compat (BaseTV (StringT max)) (StringV m _) =
    (m = max ∧ max < dimword(:256)) ∧
  bounds_compat (BaseTV (BytesT (Dynamic max))) (BytesV (Dynamic m) _) =
    (m = max ∧ max < dimword(:256)) ∧
  bounds_compat _ _ = T
End

(* Helper: word_size n ≤ n for positive n *)
Theorem word_size_le[local]:
  0 < n ⇒ word_size n ≤ n
Proof
  strip_tac >>
  simp[vfmConstantsTheory.word_size_def] >>
  `n + 31 ≤ 32 * n` by simp[] >>
  `(n + 31) DIV 32 ≤ (32 * n) DIV 32` by
    (irule DIV_LE_MONOTONE >> simp[]) >>
  `(32 * n) DIV 32 = n` by simp[MULT_TO_DIV] >>
  gvs[]
QED

(* Main dynamic bytes roundtrip *)
Theorem encode_dyn_bytes_roundtrip[local]:
  ∀bs max base storage.
    LENGTH bs ≤ max ∧ max < dimword(:256) ⇒
    decode_dyn_bytes
      (apply_writes (n2w base)
        ((0, n2w (LENGTH bs)) ::
           MAPi (λi s. (i + 1, s)) (bytes_to_slots bs))
        storage)
      base max = SOME bs
Proof
  rpt strip_tac >>
  simp[decode_dyn_bytes_def] >>
  qabbrev_tac `writes =
    (0:num, n2w (LENGTH bs) : bytes32) ::
    MAPi (λi s. (i + 1, s)) (bytes_to_slots bs)` >>
  qabbrev_tac `storage' = apply_writes (n2w base) writes storage` >>
  (* Step 1: length slot reads correctly.
     Use conj_tac to separate the n2w inequality from MEM/ALL_DISTINCT,
     and simp_tac bool_ss (not srw_ss) to avoid MAP_MAPi rewriting *)
  `lookup_storage (n2w base : bytes32) storage' = n2w (LENGTH bs)` by (
    simp[Abbr`storage'`] >>
    irule apply_writes_lookup_0 >>
    conj_tac >- (
      rpt gen_tac >> strip_tac >>
      `off < dimword(:256)` by (
        qpat_x_assum `Abbrev _`
          (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        full_simp_tac bool_ss [listTheory.MAP, pairTheory.FST, listTheory.MEM,
                               MEM_MAP_FST_MAPi, LENGTH_bytes_to_slots] >> gvs[] >>
        `word_size (LENGTH bs) ≤ LENGTH bs` by
          (Cases_on `LENGTH bs` >> gvs[word_size_le, vfmConstantsTheory.word_size_def]) >>
        irule LESS_EQ_LESS_TRANS >> qexists_tac `max` >> simp[]
      ) >>
      irule n2w_add_cancel_0 >> gvs[]
    ) >>
    qpat_x_assum `Abbrev (writes = _)`
      (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
    simp_tac bool_ss [listTheory.MAP, pairTheory.FST, listTheory.ALL_DISTINCT,
                       listTheory.MEM, ALL_DISTINCT_MAP_FST_MAPi, MEM_MAP_FST_MAPi] >>
    simp[]
  ) >>
  simp[wordsTheory.w2n_n2w] >>
  `LENGTH bs MOD dimword(:256) = LENGTH bs` by (
    irule LESS_MOD >> irule LESS_EQ_LESS_TRANS >>
    qexists_tac `max` >> simp[]
  ) >> gvs[] >>
  (* Step 2: data slots read correctly *)
  `read_slots storage' (base + 1) (word_size (LENGTH bs)) =
   bytes_to_slots bs` by (
    irule read_slots_eq_EL >> simp[LENGTH_bytes_to_slots] >>
    rpt strip_tac >> simp[Abbr`storage'`] >>
    `base + 1 + i = base + (i + 1)` by DECIDE_TAC >>
    pop_assum SUBST1_TAC >>
    irule apply_writes_lookup_hit_num >>
    conj_tac >- (
      rpt gen_tac >> strip_tac >>
      `off < dimword(:256) ∧ i + 1 < dimword(:256)` by (
        `word_size (LENGTH bs) ≤ LENGTH bs` by
          (Cases_on `LENGTH bs` >> gvs[word_size_le, vfmConstantsTheory.word_size_def]) >>
        conj_tac >- (
          qpat_x_assum `MEM _ _` mp_tac >>
          qpat_x_assum `Abbrev (writes = _)`
            (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
          full_simp_tac bool_ss [listTheory.MAP, pairTheory.FST, listTheory.MEM,
                                 MEM_MAP_FST_MAPi, LENGTH_bytes_to_slots] >>
          strip_tac >> gvs[] >>
          irule LESS_EQ_LESS_TRANS >> qexists_tac `max` >> simp[]
        ) >>
        irule LESS_EQ_LESS_TRANS >> qexists_tac `max` >> simp[]
      ) >>
      irule n2w_add_cancel >> gvs[]
    ) >>
    conj_tac >- (
      qpat_x_assum `Abbrev (writes = _)`
        (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      simp_tac bool_ss [listTheory.MAP, pairTheory.FST, listTheory.ALL_DISTINCT,
                         listTheory.MEM, ALL_DISTINCT_MAP_FST_MAPi, MEM_MAP_FST_MAPi] >>
      simp[]
    ) >>
    qpat_x_assum `Abbrev (writes = _)`
      (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
    simp_tac bool_ss [listTheory.MEM] >>
    disj2_tac >> irule MAPi_EL >> simp[LENGTH_bytes_to_slots]
  ) >> simp[slots_to_bytes_bytes_to_slots]
QED

(* roundtrip_ok for dynamic bytes *)
Theorem roundtrip_ok_dyn_bytes[local]:
  ∀max bs.
    max < dimword(:256) ∧ LENGTH bs ≤ max ⇒
    roundtrip_ok (BaseTV (BytesT (Dynamic max))) (BytesV (Dynamic max) bs)
Proof
  rw[roundtrip_ok_def] >>
  gvs[encode_value_def, AllCaseEqs(), encode_dyn_bytes_slots_def] >>
  simp[Once decode_value_def] >>
  `decode_dyn_bytes
    (apply_writes (n2w base)
      ((0, n2w (LENGTH bs)) ::
         MAPi (λi s. (i + 1,s)) (bytes_to_slots bs))
      storage) base max = SOME bs` by (
    irule encode_dyn_bytes_roundtrip >> simp[]
  ) >> simp[]
QED

(* roundtrip_ok for strings *)
Theorem roundtrip_ok_string[local]:
  ∀max s.
    max < dimword(:256) ∧ LENGTH s ≤ max ⇒
    roundtrip_ok (BaseTV (StringT max)) (StringV max s)
Proof
  rw[roundtrip_ok_def] >>
  gvs[encode_value_def, AllCaseEqs(), encode_dyn_bytes_slots_def] >>
  simp[Once decode_value_def] >>
  `decode_dyn_bytes
    (apply_writes (n2w base)
      ((0, n2w (LENGTH s)) ::
         MAPi (λi s. (i + 1,s)) (bytes_to_slots (MAP (n2w ∘ ORD) s)))
      storage) base max = SOME (MAP (n2w ∘ ORD) s)` by (
    qspecl_then [`MAP (n2w ∘ ORD) s`, `max`, `base`, `storage`]
      mp_tac encode_dyn_bytes_roundtrip >>
    simp[]
  ) >>
  simp[chr_w2n_n2w_ord]
QED

(* ===== General roundtrip_ok from well_formed_value ===== *)

(* For non-compound types, roundtrip_ok follows from well_formed_value
   and IS_SOME (encode_value tv v) *)
Theorem roundtrip_ok_from_well_formed_base[local]:
  ∀tv v.
    well_formed_value v ∧
    bounds_compat tv v ∧
    IS_SOME (encode_value tv v) ∧
    (∀tvs. tv ≠ TupleTV tvs) ∧
    (∀e bd. tv ≠ ArrayTV e bd) ∧
    (∀ftypes. tv ≠ StructTV ftypes) ∧
    (tv = NoneTV ⇒ v = NoneV) ⇒
    roundtrip_ok tv v
Proof
  rpt strip_tac >>
  Cases_on `tv` >> fs[] >>
  (* NoneTV: v = NoneV by precondition *)
  TRY (simp[roundtrip_ok_none] >> NO_TAC) >>
  (* FlagTV *)
  TRY (
    rename1 `FlagTV m` >>
    qpat_x_assum `IS_SOME _` mp_tac >>
    Cases_on `v` >>
    fs[encode_value_def, encode_base_to_slot_def, AllCaseEqs(),
       COND_RAND, COND_RATOR, well_formed_value_def] >>
    strip_tac >>
    irule roundtrip_ok_flag >> simp[] >> NO_TAC
  ) >>
  (* BaseTV bt *)
  rename1 `BaseTV bt` >>
  qpat_x_assum `IS_SOME _` mp_tac >>
  Cases_on `v` >>
  TRY (qmatch_goalsub_rename_tac `BytesV bnd _` >> Cases_on `bnd`) >>
  TRY (qmatch_goalsub_rename_tac `IntV ib _` >> Cases_on `ib`) >>
  Cases_on `bt` >>
  TRY (qmatch_goalsub_rename_tac `BytesT btbnd` >> Cases_on `btbnd`) >>
  simp[encode_value_def, encode_base_to_slot_def, AllCaseEqs(),
       COND_RAND, COND_RATOR, bounds_compat_def,
       encode_dyn_bytes_slots_def] >>
  fs[well_formed_value_def, bounds_compat_def] >>
  rpt strip_tac >>
  FIRST [
    irule roundtrip_ok_uint >> simp[],
    irule roundtrip_ok_int >> simp[],
    irule roundtrip_ok_bool,
    irule roundtrip_ok_decimal >> simp[],
    irule roundtrip_ok_string >> simp[],
    irule roundtrip_ok_fixed_bytes >> simp[],
    irule roundtrip_ok_dyn_bytes >> simp[],
    irule roundtrip_ok_address >> simp[],
    irule roundtrip_ok_flag >> simp[]
  ]
QED

(* ===== Compound Type Roundtrip Helpers ===== *)

(* Helper: type_slot_size of BaseTV is always positive *)
Theorem type_slot_size_BaseTV_pos[local,simp]:
  0 < type_slot_size (BaseTV bt)
Proof
  Cases_on `bt` >> simp[type_slot_size_def] >>
  Cases_on `b` >> simp[type_slot_size_def]
QED

(* All write offsets from encode functions are bounded by type_slot_size *)
Theorem encode_writes_bounded:
  (∀tv v writes.
     encode_value tv v = SOME writes ∧ well_formed_value v ⇒
     ∀off. MEM off (MAP FST writes) ⇒ off < type_slot_size tv) ∧
  (∀offset tvs vs writes.
     encode_tuple offset tvs vs = SOME writes ∧ wf_values vs ⇒
     ∀off. MEM off (MAP FST writes) ⇒
       offset ≤ off ∧ off < offset + type_slot_size_list tvs) ∧
  (∀tv offset sparse writes n.
     encode_static_array tv offset sparse = SOME writes ∧
     wf_sparse tv n sparse ⇒
     ∀off. MEM off (MAP FST writes) ⇒
       off < offset + n * type_slot_size tv) ∧
  (∀tv offset vs writes.
     encode_dyn_array tv offset vs = SOME writes ∧ wf_values vs ⇒
     ∀off. MEM off (MAP FST writes) ⇒
       offset ≤ off ∧ off < offset + LENGTH vs * type_slot_size tv) ∧
  (∀offset ftypes fields writes.
     encode_struct offset ftypes fields = SOME writes ∧ wf_fields fields ⇒
     ∀off. MEM off (MAP FST writes) ⇒
       offset ≤ off ∧ off < offset + type_slot_size_fields ftypes)
Proof
  ho_match_mp_tac encode_value_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[encode_value_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> gvs[MEM_MAP, MEM_APPEND, EXISTS_PROD, MEM_GENLIST,
    type_slot_size_def, well_formed_value_def,
    encode_dyn_bytes_slots_def, AllCaseEqs(),
    indexedListsTheory.MEM_MAPi, MULT_CLAUSES] >>
  (* word_size: i < word_size max *)
  TRY (
    fs[LENGTH_bytes_to_slots] >>
    irule LESS_LESS_EQ_TRANS >> first_assum (irule_at Any) >>
    simp[vfmConstantsTheory.word_size_def] >>
    irule DIV_LE_MONOTONE >> simp[] >> NO_TAC
  ) >>
  (* Static array shifted: p_1' + k * sz < n * sz via (k+1) * sz *)
  TRY (
    first_x_assum (qspec_then `p_1'` mp_tac) >>
    (impl_tac >- (qexists_tac `p_2` >> simp[])) >> strip_tac >>
    irule LESS_LESS_EQ_TRANS >>
    qexists_tac `(k + 1) * type_slot_size tv` >> simp[] >> NO_TAC
  ) >>
  (* ∀n' wf_sparse IH: specialize + instantiate *)
  TRY (
    qpat_x_assum `∀n'. wf_sparse _ _ _ ⇒ _` (qspec_then `n` mp_tac) >>
    simp[] >> strip_tac >>
    first_x_assum (qspec_then `off` mp_tac) >>
    (impl_tac >- (qexists_tac `p_2` >> simp[])) >> simp[] >> NO_TAC
  ) >>
  TRY (
    qpat_x_assum `∀n'. wf_sparse _ _ _ ⇒ _` (qspec_then `m` mp_tac) >>
    simp[] >> strip_tac >>
    first_x_assum (qspec_then `off` mp_tac) >>
    (impl_tac >- (qexists_tac `p_2` >> simp[])) >> simp[] >> NO_TAC
  ) >>
  (* DynArrayV top-level: IH + transitivity + mult monotonicity *)
  TRY (
    first_x_assum (qspec_then `off` mp_tac) >>
    (impl_tac >- (qexists_tac `p_2` >> simp[])) >> strip_tac >>
    irule LESS_LESS_EQ_TRANS >> first_assum (irule_at Any) >>
    simp[LE_MULT_RCANCEL] >> NO_TAC
  ) >>
  (* Direct IH: off or p_1' in writes *)
  TRY (
    first_x_assum (qspec_then `off` mp_tac) >>
    (impl_tac >- (qexists_tac `p_2` >> simp[])) >>
    strip_tac >> gvs[] >> NO_TAC
  ) >>
  TRY (
    first_x_assum (qspec_then `p_1'` mp_tac) >>
    (impl_tac >- (qexists_tac `p_2` >> simp[])) >>
    strip_tac >> gvs[] >> NO_TAC
  ) >>
  (* Compound internal: rest IH (conjunction) *)
  qpat_x_assum `∀off'. _ ⇒ _ ∧ _` (qspec_then `off` mp_tac) >>
  (impl_tac >- (qexists_tac `p_2` >> simp[])) >>
  strip_tac >> simp[]
QED

(* ===== Storage Agreement (decode depends only on relevant slots) ===== *)

(* Helper: read_slots agrees when individual slots agree *)
Theorem read_slots_agree[local]:
  ∀n s1 s2 offset.
    (∀i. i < n ⇒
      lookup_storage (n2w (offset + i) : bytes32) s1 =
      lookup_storage (n2w (offset + i) : bytes32) s2) ⇒
    read_slots s1 offset n = read_slots s2 offset n
Proof
  Induct >> simp[read_slots_def] >> rpt gen_tac >> strip_tac >> conj_tac
  >- (qpat_x_assum `∀i. _` (qspec_then `0` mp_tac) >> simp[])
  >> first_x_assum irule >> rw[]
  >> `n2w (i + (offset + 1)) : bytes32 = n2w (i + 1 + offset)` by simp[]
  >> pop_assum SUBST_ALL_TAC
  >> first_x_assum (qspec_then `i + 1` mp_tac) >> simp[]
QED

(* Helper: word_size is monotone *)
Theorem word_size_mono[local]:
  m ≤ n ⇒ word_size m ≤ word_size n
Proof
  rw[vfmConstantsTheory.word_size_def] >>
  irule DIV_LE_MONOTONE >> simp[]
QED

(* Helper: decode_dyn_bytes agrees when slots agree *)
Theorem decode_dyn_bytes_agree[local]:
  ∀s1 s2 offset max.
    (∀i. i < 1 + word_size max ⇒
      lookup_storage (n2w (offset + i) : bytes32) s1 =
      lookup_storage (n2w (offset + i) : bytes32) s2) ⇒
    decode_dyn_bytes s1 offset max = decode_dyn_bytes s2 offset max
Proof
  rpt strip_tac >>
  `lookup_storage (n2w offset : bytes32) s1 =
   lookup_storage (n2w offset : bytes32) s2` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[decode_dyn_bytes_def] >>
  IF_CASES_TAC >> simp[] >>
  AP_TERM_TAC >>
  irule read_slots_agree >> rw[] >>
  `n2w (offset + 1 + i) : bytes32 = n2w (offset + (i + 1))` by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  first_x_assum (qspec_then `i + 1` mp_tac) >>
  impl_tac >- (
    simp[] >>
    irule LESS_LESS_EQ_TRANS >>
    first_assum (irule_at Any) >> simp[word_size_mono]
  ) >> simp[]
QED

(* KEY LEMMA: decode only depends on slots within type_slot_size range *)
Theorem decode_storage_agree[local]:
  (∀s1 offset tv s2.
    (∀i. i < type_slot_size tv ⇒
      lookup_storage (n2w (offset + i) : bytes32) s1 =
      lookup_storage (n2w (offset + i) : bytes32) s2) ⇒
    decode_value s1 offset tv = decode_value s2 offset tv) ∧
  (∀s1 offset tvs s2.
    (∀i. i < type_slot_size_list tvs ⇒
      lookup_storage (n2w (offset + i) : bytes32) s1 =
      lookup_storage (n2w (offset + i) : bytes32) s2) ⇒
    decode_tuple s1 offset tvs = decode_tuple s2 offset tvs) ∧
  (∀s1 offset tv n s2.
    (∀i. i < n * type_slot_size tv ⇒
      lookup_storage (n2w (offset + i) : bytes32) s1 =
      lookup_storage (n2w (offset + i) : bytes32) s2) ⇒
    decode_static_array s1 offset tv n = decode_static_array s2 offset tv n) ∧
  (∀s1 offset tv n s2.
    (∀i. i < n * type_slot_size tv ⇒
      lookup_storage (n2w (offset + i) : bytes32) s1 =
      lookup_storage (n2w (offset + i) : bytes32) s2) ⇒
    decode_dyn_array s1 offset tv n = decode_dyn_array s2 offset tv n) ∧
  (∀s1 offset ftypes s2.
    (∀i. i < type_slot_size_fields ftypes ⇒
      lookup_storage (n2w (offset + i) : bytes32) s1 =
      lookup_storage (n2w (offset + i) : bytes32) s2) ⇒
    decode_struct s1 offset ftypes = decode_struct s2 offset ftypes)
Proof
  ho_match_mp_tac decode_value_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[decode_value_def, type_slot_size_def, read_slot_def] >>
  rpt strip_tac
  (* Dynamic bytes and string *)
  >> TRY (
    `decode_dyn_bytes s1 offset max = decode_dyn_bytes s2 offset max` by (
      irule decode_dyn_bytes_agree >> gen_tac >> strip_tac >>
      `n2w (offset + i) : bytes32 = n2w (i + offset)` by simp[] >>
      pop_assum SUBST_ALL_TAC >>
      first_x_assum irule >> simp[]) >>
    simp[] >> NO_TAC
  )
  (* Pass-through: TupleTV, ArrayTV Fixed, StructTV *)
  >> TRY (
    first_x_assum (qspec_then `s2` mp_tac) >>
    (impl_tac >- rw[]) >> strip_tac >> simp[] >> NO_TAC
  )
  (* ArrayTV Dynamic *)
  >> TRY (
    `lookup_storage (n2w offset : bytes32) s1 =
     lookup_storage (n2w offset : bytes32) s2` by (
      first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
    simp[] >> IF_CASES_TAC >> simp[] >> fs[] >>
    first_x_assum (qspec_then `s2` mp_tac) >>
    impl_tac >- (
      rw[] >>
      `n2w (i + (offset + 1)) : bytes32 = n2w ((i + 1) + offset)` by simp[] >>
      pop_assum SUBST_ALL_TAC >>
      first_x_assum (qspec_then `i + 1` mp_tac) >>
      impl_tac >- (
        simp[] >>
        irule LESS_LESS_EQ_TRANS >>
        qexists_tac `type_slot_size tv *
          MIN (w2n (lookup_storage (n2w offset) s2)) max` >>
        simp[] >>
        CONV_TAC(RAND_CONV(REWRITE_CONV[Once MULT_COMM])) >>
        simp[LE_MULT_LCANCEL]
      ) >> simp[]
    ) >> simp[] >> NO_TAC
  )
  (* Recursive cases: head + tail *)
  >> `decode_value s1 offset tv = decode_value s2 offset tv` by (
    qpat_x_assum `∀s2. _ ⇒ decode_value _ _ _ = _` (qspec_then `s2` mp_tac) >>
    impl_tac >- (rw[] >> first_x_assum irule >> simp[MULT_CLAUSES]) >>
    simp[]
  )
  >> qpat_x_assum `∀s2. _ ⇒ decode_value _ _ _ = _` kall_tac
  >> simp[] >> Cases_on `decode_value s1 offset tv` >> fs[]
  >> first_x_assum (qspec_then `s2` mp_tac)
  >> impl_tac
  >> TRY (
    rw[] >>
    `n2w (i + (offset + type_slot_size tv)) : bytes32 =
     n2w ((type_slot_size tv + i) + offset)` by simp[] >>
    pop_assum SUBST_ALL_TAC >>
    first_x_assum (qspec_then `type_slot_size tv + i` mp_tac) >>
    simp[MULT_CLAUSES] >> NO_TAC
  )
QED

(* ===== Decode Zero Storage ===== *)

Theorem word_to_bytes_be_zero[local]:
  word_to_bytes_be (0w : 256 word) = REPLICATE 32 (0w : word8)
Proof
  EVAL_TAC
QED

Theorem TAKE_REPLICATE[local]:
  n ≤ m ⇒ TAKE n (REPLICATE m x) = REPLICATE n x
Proof
  rw[REPLICATE_GENLIST, TAKE_GENLIST, MIN_DEF] >>
  `n = m` by simp[] >> gvs[]
QED

Theorem DROP_REPLICATE[local]:
  n ≤ m ⇒ DROP n (REPLICATE m x) = REPLICATE (m - n) x
Proof
  rw[REPLICATE_GENLIST, DROP_GENLIST, combinTheory.o_DEF, combinTheory.K_THM]
QED

Theorem enumerate_static_array_REPLICATE[local]:
  ∀n k. enumerate_static_array d k (REPLICATE n d) = []
Proof
  Induct >> rw[enumerate_static_array_def]
QED

Theorem decode_value_zero_is_default[local]:
  (∀s offset tv.
    (∀k. s k = 0w) ∧ well_formed_type_value tv ⇒
    decode_value s offset tv = SOME (default_value tv)) ∧
  (∀s offset tvs.
    (∀k. s k = 0w) ∧ EVERY well_formed_type_value tvs ⇒
    decode_tuple s offset tvs = SOME (MAP default_value tvs)) ∧
  (∀s offset tv n.
    (∀k. s k = 0w) ∧ well_formed_type_value tv ⇒
    decode_static_array s offset tv n =
      SOME (REPLICATE n (default_value tv))) ∧
  (∀s offset tv n.
    (∀k. s k = 0w) ∧ well_formed_type_value tv ⇒
    decode_dyn_array s offset tv n =
      SOME (REPLICATE n (default_value tv))) ∧
  (∀s offset ftypes.
    (∀k. s k = 0w) ∧ EVERY (well_formed_type_value o SND) ftypes ⇒
    decode_struct s offset ftypes =
      SOME (MAP (λ(id,t). (id, default_value t)) ftypes))
Proof
  ho_match_mp_tac decode_value_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[decode_value_def, default_value_def, type_slot_size_def,
       read_slot_def, lookup_storage_def, well_formed_type_value_def, ETA_THM] >>
  rpt strip_tac
  (* BytesT Dynamic / StringT *)
  >> TRY (
    simp[decode_dyn_bytes_def, lookup_storage_def,
         vfmConstantsTheory.word_size_def, read_slots_def,
         slots_to_bytes_def] >> NO_TAC
  )
  (* UintT, FlagTV *)
  >> TRY (simp[decode_base_from_slot_def] >> NO_TAC)
  (* IntT, DecimalT *)
  >> TRY (simp[decode_base_from_slot_def, integer_wordTheory.word_0_w2i] >> NO_TAC)
  (* BoolT *)
  >> TRY (simp[decode_base_from_slot_def, slot_to_bool_def] >> NO_TAC)
  (* BytesT Fixed *)
  >> TRY (
    simp[decode_base_from_slot_def, word_to_bytes_be_zero, TAKE_REPLICATE] >> NO_TAC
  )
  (* AddressT *)
  >> TRY (EVAL_TAC >> NO_TAC)
  (* TupleTV, ArrayTV Fixed, StructTV, ArrayTV Dynamic, recursive cases *)
  >> fs[] >> gvs[default_value_tuple_MAP, default_value_struct_MAP,
                 enumerate_static_array_REPLICATE, MIN_DEF]
QED

(* ===== Non-compound Roundtrip ===== *)

(* For non-compound types (BaseTV, FlagTV, NoneTV), roundtrip_ok follows
   from well_formed_value alone. Mismatch type/value pairs have encode NONE
   (vacuously true), valid pairs are handled by specific roundtrip theorems. *)
(* Helper: IS_SOME (encode_value tv v) implies bounds_compat for non-compound types *)
Theorem encode_IS_SOME_bounds_compat[local]:
  (∀tvs. tv ≠ TupleTV tvs) ∧ (∀e bd. tv ≠ ArrayTV e bd) ∧
  (∀ftypes. tv ≠ StructTV ftypes) ∧ IS_SOME (encode_value tv v) ⇒
  bounds_compat tv v
Proof
  strip_tac >> Cases_on `tv` >> fs[bounds_compat_def] >>
  Cases_on `v` >>
  TRY (rename1 `BytesV bnd _` >> Cases_on `bnd`) >>
  Cases_on `b` >>
  TRY (rename1 `BytesT btbnd` >> Cases_on `btbnd`) >>
  gvs[encode_value_def, AllCaseEqs(), encode_base_to_slot_def,
      encode_dyn_bytes_slots_def, bounds_compat_def] >>
  pop_assum mp_tac >> rpt IF_CASES_TAC >> simp[]
QED

Theorem roundtrip_ok_noncompound[local]:
  well_formed_value v ∧ well_formed_type_value tv ∧
  (∀tvs. tv ≠ TupleTV tvs) ∧ (∀e bd. tv ≠ ArrayTV e bd) ∧
  (∀ftypes. tv ≠ StructTV ftypes) ⇒
  roundtrip_ok tv v
Proof
  strip_tac >>
  reverse (Cases_on `IS_SOME (encode_value tv v)`)
  >- (Cases_on `encode_value tv v` >> gvs[roundtrip_ok_def]) >>
  Cases_on `tv` >> fs[]
  (* BaseTV *)
  >- (
    irule roundtrip_ok_from_well_formed_base >> simp[] >>
    gvs[bounds_compat_def] >>
    qpat_x_assum `IS_SOME _` mp_tac >>
    Cases_on `v` >>
    TRY (rename1 `BytesV bnd _` >> Cases_on `bnd`) >>
    Cases_on `b` >>
    TRY (rename1 `BytesT btbnd` >> Cases_on `btbnd`) >>
    simp[encode_value_def, AllCaseEqs(), encode_base_to_slot_def,
         encode_dyn_bytes_slots_def, bounds_compat_def] >>
    rpt IF_CASES_TAC >> simp[]
  )
  (* FlagTV *)
  >- (
    rename1 `FlagTV m` >>
    qpat_x_assum `IS_SOME _` mp_tac >> Cases_on `v` >>
    simp[encode_value_def, AllCaseEqs(), encode_base_to_slot_def] >>
    rpt IF_CASES_TAC >> simp[] >> gvs[] >>
    irule roundtrip_ok_flag >> gvs[well_formed_value_def]
  )
  (* NoneTV *)
  >> Cases_on `v` >> gvs[encode_value_def, roundtrip_ok_none]
QED

(* ===== Compound Roundtrip ===== *)

(* Helper: writes at non-overlapping offsets don't affect lookup *)
Theorem apply_writes_lookup_miss_num[local]:
  ∀writes base storage k.
    (∀off. MEM off (MAP FST writes) ⇒
       n2w (base + off) ≠ (n2w (base + k) : bytes32)) ⇒
    lookup_storage (n2w (base + k))
      (apply_writes (n2w base) writes storage) =
    lookup_storage (n2w (base + k)) storage
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC [GSYM nwn_eq] >>
  irule apply_writes_lookup_miss >>
  REWRITE_TAC [nwn_eq] >> gvs[]
QED

(* Helper: shifted writes can be un-shifted *)
Theorem apply_writes_MAP_shift[local]:
  ∀writes k base storage.
    apply_writes (n2w base) (MAP (λ(off,s). (off + k, s)) writes) storage =
    apply_writes (n2w (base + k)) writes storage
Proof
  REWRITE_TAC [apply_writes_shift]
QED

(* Helper: decode_value agrees with a different storage when writes are outside range *)
Theorem decode_after_disjoint_writes[local]:
  ∀tv base offset writes storage.
    (∀off. MEM off (MAP FST writes) ⇒
       ¬(offset ≤ off ∧ off < offset + type_slot_size tv)) ∧
    (∀off i. MEM off (MAP FST writes) ∧
       offset ≤ i ∧ i < offset + type_slot_size tv ∧ off ≠ i ⇒
       n2w (base + off) ≠ (n2w (base + i) : bytes32)) ⇒
    decode_value (apply_writes (n2w base) writes storage) (base + offset) tv =
    decode_value storage (base + offset) tv
Proof
  rpt strip_tac >>
  irule (CONJUNCT1 decode_storage_agree) >>
  rw[] >>
  irule apply_writes_lookup_miss_num >>
  rw[] >>
  first_x_assum (qspecl_then [`off`, `offset + i`] mp_tac) >>
  impl_tac >- (
    first_x_assum (qspec_then `off` mp_tac) >> simp[]
  ) >> simp[]
QED

(* Helper: apply_writes doesn't affect lookup at addresses outside the write set *)
Theorem apply_writes_lookup_other[local]:
  ∀writes (base : bytes32) storage (addr : bytes32).
    (∀off. MEM off (MAP FST writes) ⇒ n2w (w2n base + off) ≠ addr) ⇒
    lookup_storage addr (apply_writes base writes storage) =
    lookup_storage addr storage
Proof
  Induct >> simp[apply_writes_def] >>
  Cases >> simp[apply_writes_def] >>
  rpt strip_tac >>
  simp[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM]
QED

(* TOP-LEVEL: decode_value is unchanged when apply_writes touches a disjoint region.
   sz bounds the write offsets; the write region [off1, off1+sz) must be disjoint
   from the decode region [off2, off2+type_slot_size tv). *)
Theorem decode_value_disjoint_writes:
  ∀tv writes off1 off2 storage sz.
    (∀wr_off. MEM wr_off (MAP FST writes) ⇒ wr_off < sz) ∧
    off1 + sz ≤ dimword(:256) ∧
    off2 + type_slot_size tv ≤ dimword(:256) ∧
    (off1 + sz ≤ off2 ∨ off2 + type_slot_size tv ≤ off1) ⇒
    decode_value (apply_writes (n2w off1) writes storage) off2 tv =
    decode_value storage off2 tv
Proof
  rpt strip_tac >>
  irule (CONJUNCT1 decode_storage_agree) >>
  rpt strip_tac >>
  irule apply_writes_lookup_other >>
  REWRITE_TAC [nwn_eq] >>
  rpt strip_tac >>
  `off < sz` by res_tac >>
  gvs[wordsTheory.n2w_11]
QED

(* Helper: decode_value unchanged by disjoint apply_writes at word offset *)
Theorem decode_value_disjoint_apply_writes:
  ∀tv writes off1 off2 storage sz.
    (∀wr_off. MEM wr_off (MAP FST writes) ⇒ wr_off < sz) ∧
    off1 + sz ≤ dimword(:256) ∧
    off2 + type_slot_size tv ≤ dimword(:256) ∧
    (off1 + sz ≤ off2 ∨ off2 + type_slot_size tv ≤ off1) ⇒
    decode_value (apply_writes (n2w off1) writes storage)
      (w2n ((n2w off2):bytes32)) tv =
    decode_value storage (w2n ((n2w off2):bytes32)) tv
Proof
  rpt gen_tac >> disch_tac >>
  irule decode_value_disjoint_writes >>
  conj_tac >- (
    `off2 MOD dimword(:256) ≤ off2` by
      simp[arithmeticTheory.MOD_LESS_EQ] >>
    fs[wordsTheory.w2n_n2w]) >>
  qexists_tac `sz` >> fs[] >>
  Cases_on `off2 < dimword(:256)` >>
  simp[wordsTheory.w2n_n2w, arithmeticTheory.MOD_LESS_EQ] >>
  `off2 = dimword(:256) ∧ type_slot_size tv = 0` by simp[] >>
  gvs[]
QED

(* Helper: roundtrip_ok at an offset.
   If tv v has roundtrip_ok, then encoding v and applying the shifted writes
   at offset k allows decode at base + k to recover v. *)
Theorem roundtrip_ok_at_offset[local]:
  ∀tv v writes k base storage.
    roundtrip_ok tv v ∧
    encode_value tv v = SOME writes ⇒
    decode_value
      (apply_writes (n2w base) (MAP (λ(off,s). (off + k, s)) writes) storage)
      (base + k) tv = SOME v
Proof
  rw[roundtrip_ok_def] >>
  qpat_x_assum `∀w b s. _` (qspecl_then [`writes`, `base + k`, `storage`] mp_tac) >>
  simp[] >> strip_tac >>
  `MAP (λ(off,s). (k + off,s)) writes =
   MAP (λ(off,s). (off + k,s)) writes` by
    (irule listTheory.MAP_CONG >> simp[FORALL_PROD]) >>
  pop_assum SUBST_ALL_TAC >>
  REWRITE_TAC [apply_writes_shift] >> gvs[]
QED

(* ===== Element Roundtrip With Disjoint Extra Writes ===== *)

(* Helper: an element at offset round-trips even with extra writes,
   as long as the extra writes are at strictly higher offsets. *)
Theorem roundtrip_at_offset_disjoint[local]:
  ∀tv v offset base storage elem_writes extra_writes.
    roundtrip_ok tv v ∧
    encode_value tv v = SOME elem_writes ∧
    (∀off. MEM off (MAP FST extra_writes) ⇒
       offset + type_slot_size tv ≤ off ∧ off < dimword(:256)) ∧
    offset + type_slot_size tv ≤ dimword(:256) ⇒
    decode_value
      (apply_writes (n2w base)
        (MAP (λ(off,s). (off + offset, s)) elem_writes ++ extra_writes)
        storage)
      (base + offset) tv = SOME v
Proof
  rpt strip_tac >>
  REWRITE_TAC [apply_writes_append] >>
  irule EQ_TRANS >>
  qexists_tac `decode_value
    (apply_writes (n2w base)
      (MAP (λ(off,s). (off + offset, s)) elem_writes) storage)
    (base + offset) tv` >>
  conj_tac
  >- (
    irule decode_after_disjoint_writes >> conj_tac
    >- (
      rpt strip_tac >>
      `n2w (base + off) ≠ (n2w (base + i) : bytes32)` by (
        irule n2w_add_cancel >>
        first_x_assum (qspec_then `off` mp_tac) >> simp[]
      ) >> gvs[]
    )
    >> rpt strip_tac >>
    first_x_assum (qspec_then `off` mp_tac) >> simp[]
  )
  >> irule roundtrip_ok_at_offset >> simp[]
QED

(* ===== Compound Roundtrip Helpers ===== *)

(* Helper: tuple encode/decode roundtrip *)
Theorem encode_decode_tuple[local]:
  ∀tvs offset vs writes base storage.
    EVERY (λtv. ∀v. well_formed_value v ⇒ roundtrip_ok tv v) tvs ∧
    wf_values vs ∧ EVERY well_formed_type_value tvs ∧
    offset + type_slot_size_list tvs ≤ dimword(:256) ∧
    encode_tuple offset tvs vs = SOME writes ⇒
    decode_tuple
      (apply_writes (n2w base) writes storage) (base + offset) tvs =
    SOME vs
Proof
  Induct
  >- (Cases_on `vs` >>
      simp[encode_value_def, decode_value_def, apply_writes_nil])
  >> rpt gen_tac >> strip_tac >>
  Cases_on `vs` >- gvs[encode_value_def] >>
  qpat_x_assum `encode_tuple _ _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >>
  simp[Once decode_value_def] >>
  rename1 `encode_value htv hv = SOME hslots` >>
  rename1 `encode_tuple _ _ _ = SOME rslots` >>
  (* First element decodes correctly *)
  `decode_value (apply_writes (n2w base) writes storage)
     (base + offset) htv = SOME hv` by (
    qpat_x_assum `_ = writes` (SUBST1_TAC o SYM) >>
    irule roundtrip_at_offset_disjoint >> simp[] >>
    conj_tac >- (
      rpt strip_tac >>
      drule (el 2 (CONJUNCTS encode_writes_bounded)) >>
      disch_then (qspec_then `off` mp_tac) >>
      gvs[well_formed_value_def, type_slot_size_def]
    ) >>
    conj_tac >- gvs[type_slot_size_def] >>
    gvs[EVERY_MEM, well_formed_value_def]
  ) >> simp[] >>
  (* Rest decodes correctly via IH *)
  qpat_x_assum `_ = writes` (SUBST1_TAC o SYM) >>
  REWRITE_TAC [apply_writes_append] >>
  first_x_assum (qspecl_then
    [`offset + type_slot_size htv`, `t`, `rslots`, `base`,
     `apply_writes (n2w base) (MAP (λ(off,s). (off + offset,s)) hslots)
        storage`] mp_tac) >>
  gvs[well_formed_value_def, type_slot_size_def]
QED

(* Helper: dynamic array encode/decode roundtrip *)
Theorem encode_decode_dyn_array[local]:
  ∀vs offset tv writes base storage.
    (∀v. well_formed_value v ⇒ roundtrip_ok tv v) ∧
    wf_values vs ∧ well_formed_type_value tv ∧
    offset + LENGTH vs * type_slot_size tv ≤ dimword(:256) ∧
    encode_dyn_array tv offset vs = SOME writes ⇒
    decode_dyn_array
      (apply_writes (n2w base) writes storage) (base + offset) tv
      (LENGTH vs) =
    SOME vs
Proof
  Induct
  >- simp[encode_value_def, decode_value_def, apply_writes_nil]
  >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `encode_dyn_array _ _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >>
  simp[Once decode_value_def] >>
  rename1 `encode_value tv v = SOME elem_slots` >>
  rename1 `encode_dyn_array _ _ _ = SOME rest_writes` >>
  (* First element *)
  `decode_value (apply_writes (n2w base) writes storage)
     (base + offset) tv = SOME v` by (
    qpat_x_assum `_ = writes` (SUBST1_TAC o SYM) >>
    irule roundtrip_at_offset_disjoint >> simp[] >>
    conj_tac >- (
      rpt strip_tac >>
      drule (el 4 (CONJUNCTS encode_writes_bounded)) >>
      disch_then (qspec_then `off` mp_tac) >>
      gvs[well_formed_value_def, MULT_CLAUSES]
    ) >>
    conj_tac >- gvs[MULT_CLAUSES] >>
    gvs[well_formed_value_def]
  ) >> simp[] >>
  (* Rest via IH *)
  qpat_x_assum `_ = writes` (SUBST1_TAC o SYM) >>
  REWRITE_TAC [apply_writes_append] >>
  first_x_assum (qspecl_then
    [`offset + type_slot_size tv`, `tv`, `rest_writes`, `base`,
     `apply_writes (n2w base) (MAP (λ(off,s). (off + offset,s)) elem_slots)
        storage`] mp_tac) >>
  gvs[well_formed_value_def, MULT_CLAUSES]
QED

(* Helper: struct encode/decode roundtrip *)
Theorem encode_decode_struct[local]:
  ∀ftypes offset fields writes base storage.
    EVERY (λ(nm,tv). ∀v. well_formed_value v ⇒
             roundtrip_ok tv v) ftypes ∧
    wf_fields fields ∧ EVERY (well_formed_type_value o SND) ftypes ∧
    offset + type_slot_size_fields ftypes ≤ dimword(:256) ∧
    encode_struct offset ftypes fields = SOME writes ⇒
    decode_struct
      (apply_writes (n2w base) writes storage) (base + offset) ftypes =
    SOME fields
Proof
  Induct
  >- (Cases_on `fields` >>
      simp[encode_value_def, decode_value_def, apply_writes_nil])
  >> Cases >> rpt gen_tac >> strip_tac >>
  Cases_on `fields` >- gvs[encode_value_def] >>
  Cases_on `h` >>
  qpat_x_assum `encode_struct _ _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >>
  simp[Once decode_value_def] >>
  rename1 `encode_value tv v = SOME elem_slots` >>
  rename1 `encode_struct _ _ _ = SOME rest_writes` >>
  rename1 `(fname, tv)` >>
  (* First element *)
  `decode_value (apply_writes (n2w base)
     (MAP (λ(off,s). (off + offset,s)) elem_slots ⧺ rest_writes) storage)
     (base + offset) tv = SOME v` by (
    irule roundtrip_at_offset_disjoint >> simp[] >>
    conj_tac >- (
      rpt strip_tac >>
      drule (el 5 (CONJUNCTS encode_writes_bounded)) >>
      disch_then (qspec_then `off` mp_tac) >>
      gvs[well_formed_value_def, type_slot_size_def]
    ) >>
    conj_tac >- gvs[type_slot_size_def] >>
    gvs[well_formed_value_def]
  ) >> simp[] >>
  (* Rest via IH *)
  REWRITE_TAC [apply_writes_append] >>
  first_x_assum (qspecl_then
    [`offset + type_slot_size tv`, `t`, `rest_writes`, `base`,
     `apply_writes (n2w base) (MAP (λ(off,s). (off + offset,s)) elem_slots)
        storage`] mp_tac) >>
  gvs[well_formed_value_def, type_slot_size_def]
QED

(* Helper: wf_sparse implies well_formed_value for each entry *)
Theorem wf_sparse_well_formed[local]:
  ∀sparse tv n k v.
    wf_sparse tv n sparse ∧ MEM (k,v) sparse ⇒ well_formed_value v
Proof
  Induct >> simp[well_formed_value_def] >>
  Cases >> rw[well_formed_value_def] >> res_tac >> simp[]
QED

(* Helper: lower bound on encode_static_array offsets *)
Theorem encode_static_array_offset_lower[local]:
  ∀sparse tv offset writes m.
    encode_static_array tv offset sparse = SOME writes ∧
    (∀k v. MEM (k,v) sparse ⇒ well_formed_value v) ∧
    (∀key. MEM key (MAP FST sparse) ⇒ m ≤ key) ⇒
    ∀off. MEM off (MAP FST writes) ⇒ offset + m * type_slot_size tv ≤ off
Proof
  Induct >> simp[] >>
  Cases >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `encode_static_array _ _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >>
  gvs[MEM_MAP, EXISTS_PROD, MEM_APPEND]
  >- (
    `m ≤ q` by metis_tac[] >>
    irule LESS_EQ_TRANS >>
    rename1 `MEM (eoff, _) _` >>
    qexists_tac `q * type_slot_size tv` >> simp[]
  )
  >- (
    first_x_assum irule >> simp[] >>
    metis_tac[]
  )
QED

(* Helper: apply_writes with agreeing storages gives agreeing results *)
Theorem apply_writes_storage_agree[local]:
  ∀writes base s1 s2.
    (∀k. lookup_storage (n2w (base + k)) s1 =
         lookup_storage (n2w (base + k)) s2) ⇒
    ∀k. lookup_storage (n2w (base + k))
          (apply_writes (n2w base) writes s1) =
        lookup_storage (n2w (base + k))
          (apply_writes (n2w base) writes s2)
Proof
  Induct >> simp[apply_writes_def] >>
  Cases >> rpt gen_tac >> strip_tac >>
  simp[apply_writes_def] >>
  first_x_assum irule >> rw[] >>
  rw[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM] >>
  gvs[lookup_storage_def]
QED

(* Helper: static array - each sparse entry decodes correctly *)
Theorem encode_decode_static_array[local]:
  ∀sparse tv n offset writes base storage.
    (∀v. well_formed_value v ⇒ roundtrip_ok tv v) ∧
    wf_sparse tv n sparse ∧ well_formed_type_value tv ∧
    SORTED $< (MAP FST sparse) ∧
    offset + n * type_slot_size tv ≤ dimword(:256) ∧
    encode_static_array tv offset sparse = SOME writes ⇒
    ∀k v. MEM (k, v) sparse ⇒
      decode_value
        (apply_writes (n2w base) writes storage)
        (base + offset + k * type_slot_size tv) tv = SOME v
Proof
  Induct
  >- simp[]
  >> Cases >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `encode_static_array _ _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >>
  rename1 `encode_value tv v' = SOME elem_slots` >>
  rename1 `encode_static_array _ _ _ = SOME rest_writes` >>
  rename1 `(k', v')`
  (* Head entry: k = k', v = v' *)
  >- (
    gvs[] >>
    irule roundtrip_at_offset_disjoint >>
    simp[] >>
    fs[well_formed_value_def] >>
    rpt conj_tac
    (* Conjunct 1: ∀off. MEM off (MAP FST rest_writes) ⇒ bounds *)
    >- (
      rpt strip_tac
      (* lower bound: offset + tss + k*tss ≤ off *)
      >- (
        qspecl_then [`sparse`, `tv`, `offset`, `rest_writes`, `SUC k`]
          mp_tac encode_static_array_offset_lower >>
        impl_tac >- (
          simp[] >>
          conj_tac >- metis_tac[wf_sparse_well_formed] >>
          rpt strip_tac >>
          `k < key` suffices_by simp[] >>
          gvs[sortingTheory.SORTED_EQ]
        ) >>
        disch_then drule >> simp[MULT_CLAUSES]
      )
      (* upper bound: off < dimword(:256) *)
      >- (
        drule_all (el 3 (CONJUNCTS encode_writes_bounded)) >>
        strip_tac >>
        irule LESS_LESS_EQ_TRANS >>
        qexists_tac `offset + n * type_slot_size tv` >> simp[]
      )
    )
    (* Conjunct 2: offset + tss + k*tss ≤ dimword(:256) *)
    >- (
      irule LESS_EQ_TRANS >>
      qexists_tac `offset + n * type_slot_size tv` >> simp[] >>
      `type_slot_size tv + k * type_slot_size tv =
       SUC k * type_slot_size tv` by simp[MULT_CLAUSES, ADD_COMM] >>
      pop_assum SUBST1_TAC >> simp[]
    )
  )
  (* Tail entry: MEM (k, v) sparse - IH storage is ∀-quantified *)
  >> (
    qpat_x_assum `_ = writes` (SUBST1_TAC o SYM) >>
    REWRITE_TAC [apply_writes_append] >>
    `base + (offset + k * type_slot_size tv) =
     base + offset + k * type_slot_size tv` by simp[] >>
    pop_assum SUBST1_TAC >>
    first_x_assum irule >>
    gvs[well_formed_value_def, sortingTheory.SORTED_EQ] >>
    qexists_tac `n` >> simp[]
  )
QED

(* Helper: reading slot 0 after cons write with disjoint tail *)
Theorem read_slot_cons_0[local]:
  ∀slots val0 base storage.
    (∀off. MEM off (MAP FST slots) ⇒
      n2w (base + off) ≠ (n2w base : bytes32)) ⇒
    read_slot (apply_writes (n2w base) ((0, val0) :: slots) storage) base =
    val0
Proof
  rpt strip_tac >>
  simp[read_slot_def] >>
  `(0:num, val0) :: slots = [(0, val0)] ++ slots` by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  REWRITE_TAC [apply_writes_append] >>
  qspecl_then [`slots`, `base`,
    `apply_writes (n2w base) [(0, val0)] storage`, `0`]
    (mp_tac o REWRITE_RULE [arithmeticTheory.ADD_0])
    apply_writes_lookup_miss_num >>
  impl_tac >- (rpt strip_tac >> gvs[]) >>
  disch_then SUBST1_TAC >>
  REWRITE_TAC [GSYM read_slot_def] >>
  simp[read_slot_after_apply_writes_single]
QED

(* Helper: element slot size bounded by list total *)
Theorem type_slot_size_list_MEM[local]:
  ∀tvs tv. MEM tv tvs ⇒ type_slot_size tv ≤ type_slot_size_list tvs
Proof
  Induct >> simp[type_slot_size_def] >>
  rpt strip_tac >> gvs[type_slot_size_def] >>
  first_x_assum drule >> simp[]
QED

(* Helper: field slot size bounded by fields total *)
Theorem type_slot_size_fields_MEM[local]:
  ∀fields nm tv.
    MEM (nm,tv) fields ⇒
    type_slot_size tv ≤ type_slot_size_fields fields
Proof
  Induct >> simp[type_slot_size_def, FORALL_PROD] >>
  rpt strip_tac >> gvs[type_slot_size_def] >>
  first_x_assum drule >> simp[]
QED

(* Helper: MEM implies element size < TupleTV size *)
Theorem MEM_TupleTV_type_value_size[local]:
  ∀tvs tv. MEM tv tvs ⇒ type_value_size tv < type_value_size (TupleTV tvs)
Proof
  Induct >> simp[type_value_size_def] >>
  rpt strip_tac >> gvs[type_value_size_def] >>
  first_x_assum drule >> simp[]
QED

(* Helper: MEM in fields implies type_value_size < StructTV size *)
Theorem MEM_StructTV_type_value_size[local]:
  ∀(fields : (string # type_value) list) nm tv.
    MEM (nm,tv) fields ⇒
    type_value_size tv < type_value_size (StructTV fields)
Proof
  Induct >> simp[type_value_size_def, FORALL_PROD] >>
  rpt strip_tac >> gvs[type_value_size_def] >>
  first_x_assum drule >> simp[]
QED

(* Helper: decode_static_array from individual positions *)
Theorem decode_static_array_GENLIST[local]:
  ∀n t s off f.
    (∀i. i < n ⇒ decode_value s (off + i * type_slot_size t) t = SOME (f i)) ⇒
    decode_static_array s off t n = SOME (GENLIST f n)
Proof
  Induct >- simp[Once decode_value_def] >>
  rpt strip_tac >>
  simp[Once decode_value_def, GENLIST_CONS] >>
  `decode_value s off t = SOME (f 0)` by (
    first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[] >>
  first_x_assum (qspecl_then [`t`, `s`, `off + type_slot_size t`,
    `f o SUC`] mp_tac) >>
  impl_tac >- (
    rpt strip_tac >>
    first_x_assum (qspec_then `SUC i` mp_tac) >>
    simp[MULT_CLAUSES]) >>
  strip_tac >> simp[]
QED

(* Helper: enumerate_static_array roundtrip with GENLIST *)
Theorem enumerate_GENLIST_roundtrip[local]:
  ∀n k (sparse : (num # 'a) list) (d : 'a).
    SORTED $< (MAP FST sparse) ∧
    (∀j v. MEM (j,v) sparse ⇒ k ≤ j ∧ j < k + n ∧ v ≠ d) ⇒
    enumerate_static_array d k
      (GENLIST (λi. case ALOOKUP sparse (k+i) of
                    | SOME v => v | NONE => d) n) = sparse
Proof
  Induct >- (
    rpt strip_tac >> Cases_on `sparse` >> simp[enumerate_static_array_def] >>
    PairCases_on `h` >>
    first_x_assum (qspecl_then [`h0`, `h1`] mp_tac) >>
    impl_tac >- simp[] >> strip_tac >> gvs[]
  ) >>
  rpt strip_tac >>
  simp[GENLIST_CONS, enumerate_static_array_def] >>
  Cases_on `ALOOKUP sparse k`
  >- (
    (* ALOOKUP sparse k = NONE: head is d, skip *)
    simp[] >>
    `(λi. case ALOOKUP sparse (i + k) of NONE => d | SOME v => v) ∘ SUC =
     (λi. case ALOOKUP sparse (SUC k + i) of NONE => d | SOME v => v)` by
      simp[FUN_EQ_THM, o_THM, ADD_CLAUSES] >>
    pop_assum SUBST1_TAC >>
    first_x_assum irule >> simp[] >>
    rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
    (* j ≠ k since ALOOKUP sparse k = NONE but MEM (j,v) sparse *)
    `j ≠ k` suffices_by simp[] >>
    CCONTR_TAC >> gvs[] >>
    qpat_x_assum `ALOOKUP _ _ = NONE` mp_tac >>
    simp[alistTheory.ALOOKUP_FAILS] >>
    qexists_tac `v` >> simp[]
  )
  >> (
    (* ALOOKUP sparse k = SOME x: head is x, include (k, x) *)
    rename1 `ALOOKUP sparse k = SOME v0` >>
    (* sparse must start with (k, v0) since all keys ≥ k and sorted *)
    Cases_on `sparse` >> gvs[] >>
    PairCases_on `h` >> gvs[] >>
    `h0 = k` by (
      CCONTR_TAC >>
      `k ≤ h0` by (first_x_assum (qspecl_then [`h0`, `h1`] mp_tac) >> simp[]) >>
      `ALOOKUP t k = SOME v0` by gvs[] >>
      drule alistTheory.ALOOKUP_MEM >> strip_tac >>
      fs[sortingTheory.less_sorted_eq] >>
      `MEM k (MAP FST t)` by (rw[MEM_MAP] >> qexists_tac `(k,v0)` >> simp[]) >>
      res_tac >> gvs[]
    ) >>
    gvs[] >>
    (* gvs already substituted k=h0, v0=h1, resolved if-then-else *)
    `(λi. case if i = 0 then SOME h1 else ALOOKUP t (h0 + i) of
            NONE => d | SOME v => v) ∘ SUC =
     (λi. case ALOOKUP t (SUC h0 + i) of NONE => d | SOME v => v)` by
      simp[FUN_EQ_THM, o_THM, ADD_CLAUSES] >>
    pop_assum SUBST1_TAC >>
    `enumerate_static_array d (SUC h0)
       (GENLIST (λi. case ALOOKUP t (i + SUC h0) of NONE => d | SOME v => v) n) = t`
      suffices_by simp[Once ADD_COMM] >>
    first_x_assum irule >>
    gvs[sortingTheory.less_sorted_eq] >>
    rpt strip_tac >>
    first_x_assum (qspecl_then [`j`, `v`] mp_tac) >> simp[] >>
    strip_tac >>
    `MEM j (MAP FST t)` by (rw[MEM_MAP] >> qexists_tac `(j,v)` >> simp[]) >>
    res_tac >> simp[]
  )
QED


(* Helper: encode_static_array writes only at offsets for existing keys *)
Theorem encode_static_array_miss[local]:
  ∀sparse tv writes i.
    encode_static_array tv 0 sparse = SOME writes ∧
    (∀k v. MEM (k,v) sparse ⇒ well_formed_value v) ∧
    ALOOKUP sparse i = NONE ⇒
    ∀off. MEM off (MAP FST writes) ⇒
      ¬(i * type_slot_size tv ≤ off ∧
        off < i * type_slot_size tv + type_slot_size tv)
Proof
  Induct >- simp[Once encode_value_def] >>
  Cases >> rpt gen_tac >> strip_tac >>
  rename1 `(hk, hv) :: rest` >>
  qpat_x_assum `encode_static_array _ _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >>
  rename1 `encode_value tv hv = SOME elem_slots` >>
  rename1 `encode_static_array tv 0 rest = SOME rest_writes` >>
  qpat_x_assum `_ = writes` (SUBST_ALL_TAC o SYM) >>
  gvs[MAP_APPEND, MEM_APPEND, MEM_MAP, EXISTS_PROD]
  (* Case 1: off from shifted elem_slots *)
  >- (
    CCONTR_TAC >> gvs[] >>
    `hk ≠ i` by (qpat_x_assum `ALOOKUP _ _ = NONE` mp_tac >> simp[]) >>
    `well_formed_value hv` by (
      first_x_assum irule >> qexists_tac `hk` >> simp[]) >>
    `p_1' < type_slot_size tv` by (
      qspecl_then [`tv`, `hv`, `elem_slots`]
        mp_tac (CONJUNCT1 encode_writes_bounded) >>
      simp[] >> strip_tac >>
      first_x_assum (qspec_then `p_1'` mp_tac) >>
      simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]
    ) >>
    `hk < i ∨ i < hk` by simp[]
    >- (`(hk + 1) * type_slot_size tv ≤ i * type_slot_size tv` by
          simp[LE_MULT_RCANCEL] >> gvs[])
    >> (`(i + 1) * type_slot_size tv ≤ hk * type_slot_size tv` by
          simp[LE_MULT_RCANCEL] >> gvs[])
  )
  (* Case 2: off from rest_writes *)
  >> (
    qpat_x_assum `∀tv' writes i'. _`
      (qspecl_then [`tv`, `rest_writes`, `i`] mp_tac) >>
    simp[] >>
    impl_tac >- metis_tac[] >>
    disch_then (qspec_then `off` mp_tac) >> simp[] >>
    metis_tac[]
  )
QED

(* Helper: GENLIST zeros make lookup return 0w *)
Theorem genlist_zeros_lookup[local]:
  ∀m base storage k.
    k < m ∧ m ≤ dimword(:256) ⇒
    lookup_storage (n2w (base + k) : bytes32)
      (apply_writes (n2w base) (GENLIST (λi. (i, 0w : bytes32)) m) storage) = 0w
Proof
  rpt strip_tac >>
  irule apply_writes_lookup_hit_num >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    irule n2w_add_cancel >>
    gvs[MAP_GENLIST, MEM_GENLIST, o_DEF]
  ) >>
  simp[MAP_GENLIST, o_DEF, ALL_DISTINCT_GENLIST, MEM_GENLIST]
QED


(* Helper: Static array roundtrip *)
Theorem roundtrip_static_array[local]:
  ∀tv n sparse nonzeros base storage.
    (∀v. well_formed_value v ⇒ roundtrip_ok tv v) ∧
    wf_sparse tv n sparse ∧ well_formed_type_value tv ∧
    SORTED $< (MAP FST sparse) ∧
    n * type_slot_size tv ≤ dimword(:256) ∧
    encode_static_array tv 0 sparse = SOME nonzeros ⇒
    decode_value
      (apply_writes (n2w base)
         (GENLIST (λi. (i,0w)) (n * type_slot_size tv) ++ nonzeros) storage)
      base (ArrayTV tv (Fixed n)) = SOME (ArrayV (SArrayV tv n sparse))
Proof
  rpt strip_tac >>
  simp[Once decode_value_def] >>
  qabbrev_tac `f = λi. case ALOOKUP sparse i of
    SOME v => v | NONE => default_value tv` >>
  (* Step 1: decode_static_array gives GENLIST f n *)
  sg `decode_static_array
     (apply_writes (n2w base)
        (GENLIST (λi. (i,0w)) (n * type_slot_size tv) ⧺ nonzeros) storage)
     base tv n = SOME (GENLIST f n)` >- (
    irule decode_static_array_GENLIST >>
    rpt strip_tac >> simp[Abbr`f`] >>
    REWRITE_TAC [apply_writes_append] >>
    Cases_on `ALOOKUP sparse i` >> simp[]
    (* NONE case first (Cases_on puts NONE as first subgoal) *)
    >- (
      `decode_value (λk. 0w) (base + i * type_slot_size tv) tv =
         SOME (default_value tv)` by
        simp[CONJUNCT1 decode_value_zero_is_default] >>
      pop_assum (SUBST1_TAC o SYM) >>
      irule (CONJUNCT1 decode_storage_agree) >>
      rpt gen_tac >> strip_tac >>
      rename1 `j < type_slot_size tv` >>
      simp[lookup_storage_def] >>
      `i * type_slot_size tv + j < n * type_slot_size tv` by (
        irule LESS_LESS_EQ_TRANS >>
        qexists_tac `(i + 1) * type_slot_size tv` >>
        simp[LE_MULT_RCANCEL]) >>
      ONCE_REWRITE_TAC [GSYM vfmStateTheory.lookup_storage_def] >>
      `lookup_storage (n2w (base + (j + i * type_slot_size tv)))
         (apply_writes (n2w base) nonzeros
           (apply_writes (n2w base)
              (GENLIST (λi. (i,0w)) (n * type_slot_size tv)) storage)) =
       lookup_storage (n2w (base + (j + i * type_slot_size tv)))
         (apply_writes (n2w base)
            (GENLIST (λi. (i,0w)) (n * type_slot_size tv)) storage)` by (
        irule apply_writes_lookup_miss_num >>
        rpt gen_tac >> strip_tac >>
        irule n2w_add_cancel >>
        (* irule gives: off ≠ k ∧ k < dimword ∧ off < dimword *)
        conj_tac >- (
          CCONTR_TAC >> gvs[] >>
          `∀k v. MEM (k,v) sparse ⇒ well_formed_value v` by
            metis_tac[wf_sparse_well_formed] >>
          qspecl_then [`sparse`, `tv`, `nonzeros`, `i`]
            mp_tac encode_static_array_miss >>
          impl_tac >- (
            rpt conj_tac >> first_x_assum ACCEPT_TAC
          ) >>
          disch_then (qspec_then `j + i * type_slot_size tv` mp_tac) >>
          simp[]
        ) >>
        conj_tac >- (
          irule LESS_LESS_EQ_TRANS >>
          qexists_tac `n * type_slot_size tv` >> gvs[]
        ) >>
        irule LESS_LESS_EQ_TRANS >>
        qexists_tac `n * type_slot_size tv` >> conj_tac >- (
          qspecl_then [`tv`, `0`, `sparse`, `nonzeros`, `n`]
            mp_tac (el 3 (CONJUNCTS encode_writes_bounded)) >>
          impl_tac >- simp[] >>
          disch_then drule >> simp[]
        ) >> gvs[]
      ) >> simp[] >>
      irule genlist_zeros_lookup >> simp[]
    )
    (* SOME case: use encode_decode_static_array *)
    >> (
      rename1 `_ = SOME v0` >>
      qspecl_then [`sparse`, `tv`, `n`, `0`, `nonzeros`, `base`,
        `apply_writes (n2w base)
           (GENLIST (λi. (i,0w)) (n * type_slot_size tv)) storage`]
        mp_tac encode_decode_static_array >>
      impl_tac >- gvs[] >>
      disch_then (qspecl_then [`i`, `v0`] mp_tac) >>
      impl_tac >- metis_tac[alistTheory.ALOOKUP_MEM] >>
      simp[]
    )
  ) >> simp[] >>
  (* Step 2: enumerate_static_array gives back sparse *)
  simp[Abbr`f`] >>
  qspecl_then [`n`, `0`, `sparse`, `default_value tv`]
    mp_tac enumerate_GENLIST_roundtrip >> simp[] >>
  strip_tac >> pop_assum mp_tac >> impl_tac >- (
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `wf_sparse _ _ _` mp_tac >>
    pop_assum mp_tac >>
    MAP_EVERY qid_spec_tac [`sparse`] >>
    Induct >> simp[well_formed_value_def] >>
    Cases >> rw[well_formed_value_def] >> gvs[] >>
    res_tac >> gvs[]
  ) >> simp[]
QED

(* Helper: Dynamic array roundtrip (n > 0 case) *)
Theorem roundtrip_dyn_array[local]:
  ∀tv n vs slots base storage.
    (∀v. well_formed_value v ⇒ roundtrip_ok tv v) ∧
    n ≠ 0 ∧
    encode_dyn_array tv 1 vs = SOME slots ∧
    n * type_slot_size tv + 1 ≤ dimword(:256) ∧
    0 < type_slot_size tv ∧
    well_formed_type_value tv ∧
    well_formed_value (ArrayV (DynArrayV tv n vs)) ⇒
    decode_value (apply_writes (n2w base) ((0,n2w (LENGTH vs))::slots) storage)
      base (ArrayTV tv (Dynamic n)) = SOME (ArrayV (DynArrayV tv n vs))
Proof
  rpt strip_tac >>
  simp[Once decode_value_def] >>
  (* read_slot at base gives n2w (LENGTH vs) *)
  `read_slot (apply_writes (n2w base)
      ((0,n2w (LENGTH vs))::slots) storage) base =
    n2w (LENGTH vs)` by (
    irule read_slot_cons_0 >>
    gen_tac >> strip_tac >>
    irule n2w_add_cancel_0 >>
    `wf_values vs ∧ LENGTH vs ≤ n` by gvs[well_formed_value_def] >>
    drule (el 4 (CONJUNCTS encode_writes_bounded)) >>
    disch_then drule >> strip_tac >>
    pop_assum drule >> strip_tac >>
    `LENGTH vs * type_slot_size tv ≤ n * type_slot_size tv` by (
      irule LESS_MONO_MULT >> simp[]
    ) >>
    conj_tac >- simp[] >>
    irule LESS_LESS_EQ_TRANS >>
    qexists_tac `n * type_slot_size tv + 1` >>
    simp[]
  ) >>
  (* establish bounds before simp *)
  `LENGTH vs ≤ n` by gvs[well_formed_value_def] >>
  `n * type_slot_size tv < dimword(:256)` by gvs[] >>
  `LENGTH vs ≤ n * type_slot_size tv` by (
    irule LESS_EQ_TRANS >> qexists_tac `n` >>
    simp[LE_MULT_CANCEL_LBARE]
  ) >>
  `LENGTH vs < dimword(:256)` by gvs[] >>
  simp[] >>
  `MIN (LENGTH vs) n = LENGTH vs` by gvs[MIN_DEF] >>
  `decode_dyn_array
      (apply_writes (n2w base) ((0,n2w (LENGTH vs))::slots) storage)
      (base + 1) tv (LENGTH vs) = SOME vs` suffices_by simp[] >>
  `(0:num, n2w (LENGTH vs) : bytes32) :: slots =
    [(0, n2w (LENGTH vs))] ++ slots` by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  REWRITE_TAC [apply_writes_append] >>
  irule encode_decode_dyn_array >>
  simp[] >>
  gvs[well_formed_value_def] >>
  `LENGTH vs * type_slot_size tv ≤ n * type_slot_size tv` by (
    irule LESS_MONO_MULT >> simp[]
  ) >>
  irule LESS_EQ_TRANS >>
  qexists_tac `n * type_slot_size tv + 1` >> simp[]
QED

(* ===== Main Roundtrip Theorem ===== *)

Theorem roundtrip_all:
  ∀tv v.
    well_formed_value v ∧ well_formed_type_value tv ⇒
    roundtrip_ok tv v
Proof
  completeInduct_on `type_value_size tv` >>
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  Cases_on `tv`
  (* BaseTV, FlagTV, NoneTV *)
  >> TRY (
    irule roundtrip_ok_noncompound >>
    simp[well_formed_value_def, well_formed_type_value_def] >> NO_TAC
  )
  (* TupleTV tvs *)
  >> TRY (
    rename1 `TupleTV tvs` >>
    (* Bridge IH: use size < to get unconditional roundtrip *)
    `EVERY (λtv. ∀v'. well_formed_value v' ⇒ roundtrip_ok tv v') tvs` by (
      simp[EVERY_MEM] >> rpt strip_tac >>
      rename1 `MEM tv' tvs` >>
      `type_value_size tv' < v` by (
        qpat_x_assum `v = _` SUBST1_TAC >>
        irule MEM_TupleTV_type_value_size >> simp[]
      ) >>
      first_x_assum drule >> strip_tac >>
      pop_assum (qspec_then `tv'` mp_tac) >> simp[] >>
      strip_tac >> first_x_assum irule >> simp[] >>
      fs[well_formed_type_value_def, EVERY_MEM] >>
      first_x_assum drule >> simp[]
    ) >>
    (* Expand roundtrip_ok in goal only *)
    CONV_TAC (REWR_CONV roundtrip_ok_def) >>
    rpt strip_tac >>
    Cases_on `v'` >> gvs[encode_value_def] >>
    Cases_on `a` >> gvs[encode_value_def, AllCaseEqs()] >>
    simp[Once decode_value_def] >>
    `decode_tuple (apply_writes (n2w base) writes storage)
       base tvs = SOME l` suffices_by simp[] >>
    qspecl_then [`tvs`, `0`, `l`, `writes`, `base`, `storage`]
      mp_tac encode_decode_tuple >> simp[] >>
    gvs[well_formed_value_def, well_formed_type_value_def, type_slot_size_def,
        ETA_THM] >> NO_TAC
  )
  (* ArrayTV tv' b *)
  >- (
    rename1 `ArrayTV tv' b` >>
    CONV_TAC (REWR_CONV roundtrip_ok_def) >>
    rpt strip_tac >>
    Cases_on `b`
    (* ArrayTV tv' (Fixed n) *)
    >- (
      Cases_on `v'` >> gvs[encode_value_def] >>
      Cases_on `a` >> gvs[encode_value_def, AllCaseEqs()] >>
      (* n = 0: empty array *)
      Cases_on `n = 0` >- (
        `l = []` by (
          Cases_on `l` >> gvs[] >>
          PairCases_on `h` >> gvs[well_formed_value_def]
        ) >>
        gvs[encode_value_def, apply_writes_def] >>
        simp[Once decode_value_def] >>
        simp[decode_value_def, enumerate_static_array_def]
      ) >>
      (* n > 0: use roundtrip_static_array *)
      irule roundtrip_static_array >>
      gvs[well_formed_value_def, well_formed_type_value_def, type_slot_size_def] >>
      rpt strip_tac >>
      first_x_assum (qspec_then `type_value_size t` mp_tac) >> simp[] >>
      disch_then (qspec_then `t` mp_tac) >> simp[] >>
      disch_then irule >> simp[]
    )
    (* ArrayTV tv' (Dynamic n) *)
    >> (
      Cases_on `v'` >> gvs[encode_value_def] >>
      Cases_on `a` >> gvs[encode_value_def, AllCaseEqs()] >>
      rename1 `encode_dyn_array tv' 1 vs = SOME slots` >>
      Cases_on `n = 0` >- (
        `vs = []` by (
          gvs[well_formed_value_def] >> Cases_on `vs` >> gvs[]
        ) >>
        gvs[encode_value_def] >>
        simp[read_slot_after_apply_writes_single, decode_value_def]
      ) >>
      irule roundtrip_dyn_array >> simp[] >>
      conj_tac >- (
        rpt strip_tac >>
        first_x_assum (qspec_then `type_value_size tv'` mp_tac) >>
        simp[] >>
        disch_then (qspec_then `tv'` mp_tac) >> simp[] >>
        disch_then irule >>
        gvs[well_formed_type_value_def, type_slot_size_def]
      ) >>
      gvs[well_formed_type_value_def, type_slot_size_def]
    )
  )
  (* StructTV ftypes *)
  >> (
    rename1 `StructTV ftypes` >>
    (* Bridge IH: use size < to get unconditional roundtrip *)
    `EVERY (λ(nm,tv). ∀v'. well_formed_value v' ⇒
             roundtrip_ok tv v') ftypes` by (
      simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
      rename1 `MEM (nm, tv') ftypes` >>
      `type_value_size tv' < v` by (
        qpat_x_assum `v = _` SUBST1_TAC >>
        metis_tac[MEM_StructTV_type_value_size]
      ) >>
      first_x_assum drule >> strip_tac >>
      pop_assum (qspec_then `tv'` mp_tac) >> simp[] >>
      strip_tac >> first_x_assum irule >> simp[] >>
      fs[well_formed_type_value_def, EVERY_MEM] >>
      first_x_assum drule >> simp[]
    ) >>
    (* Expand roundtrip_ok in goal only *)
    CONV_TAC (REWR_CONV roundtrip_ok_def) >>
    rpt strip_tac >>
    Cases_on `v'` >> gvs[encode_value_def, AllCaseEqs()] >>
    simp[Once decode_value_def] >>
    rename1 `encode_struct 0 ftypes fields = SOME writes` >>
    `decode_struct (apply_writes (n2w base) writes storage)
       base ftypes = SOME fields` suffices_by simp[] >>
    qspecl_then [`ftypes`, `0`, `fields`, `writes`, `base`, `storage`]
      mp_tac encode_decode_struct >> simp[] >>
    gvs[well_formed_value_def, well_formed_type_value_def, type_slot_size_def,
        ETA_THM]
  )
QED
