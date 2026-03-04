(*
 * vyperStorageRoundtripScript.sml
 *
 * Storage encode/decode roundtrip properties.
 *
 * TOP-LEVEL:
 *   word_to_bytes_be_word_of_bytes_be - reverse byte roundtrip (LENGTH 32)
 *   word_of_bytes_be_word_to_bytes_be - forward byte roundtrip
 *   roundtrip_ok_def - predicate: type/value pair round-trips through storage
 *)

Theory vyperStorageRoundtrip
Ancestors
  vyperStorage vfmState byte list rich_list combin bitstring bit sorting
  arithmetic pair indexedLists vfmConstants
Libs
  wordsLib dep_rewrite

(* ===== Byte Roundtrip ===== *)

Theorem LENGTH_word_to_bytes_be_256:
  LENGTH (word_to_bytes_be (w : bytes32)) = 32
Proof
  simp[word_to_bytes_be_def, LENGTH_word_to_bytes]
QED

Theorem word_to_bytes_be_word_of_bytes_be:
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

Theorem word_of_bytes_be_word_to_bytes_be:
  word_of_bytes_be (word_to_bytes_be (w : bytes32)) = w
Proof
  simp[word_to_bytes_be_def, word_of_bytes_be_def,
       word_of_bytes_word_to_bytes]
QED

(* ===== apply_writes Properties ===== *)

Theorem apply_writes_nil:
  apply_writes base [] storage = storage
Proof
  simp[apply_writes_def]
QED

Theorem read_slot_after_apply_writes_single:
  read_slot (apply_writes (n2w base) [(0, val0)] storage) base = val0
Proof
  simp[read_slot_def, apply_writes_def, lookup_storage_def, update_storage_def,
       APPLY_UPDATE_THM]
QED

Theorem apply_writes_append:
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

Theorem apply_writes_shift:
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

Theorem apply_writes_lookup_miss:
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

Theorem apply_writes_lookup_hit:
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

Theorem slots_to_bytes_bytes_to_slots:
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

Theorem chr_w2n_n2w_ord:
  ∀s. MAP (CHR o w2n) (MAP ((n2w : num -> word8) o ORD) s) = s
Proof
  Induct >> simp[wordsTheory.w2n_n2w] >>
  gen_tac >>
  `ORD h < 256` by simp[stringTheory.ORD_BOUND] >>
  `dimword(:8) = 256` by EVAL_TAC >>
  gvs[stringTheory.CHR_ORD]
QED

(* ===== Roundtrip Predicate ===== *)

Definition roundtrip_ok_def:
  roundtrip_ok tv v ⇔
    ∀writes base storage.
      encode_value tv v = SOME writes ⇒
      decode_value (apply_writes (n2w base) writes storage) base tv = SOME v
End

(* ===== Helper: single-slot base type roundtrip ===== *)

(* Helper: for non-dynamic, non-string base types, the roundtrip works
   when encode_base_to_slot succeeds and decode_base_from_slot inverts it *)
Theorem decode_value_single_slot:
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

Theorem roundtrip_ok_bool:
  ∀b. roundtrip_ok (BaseTV BoolT) (BoolV b)
Proof
  rw[] >> irule decode_value_single_slot >> simp[] >>
  qexists_tac `bool_to_slot b` >>
  simp[encode_base_to_slot_def, decode_base_from_slot_def,
       slot_to_bool_bool_to_slot]
QED

(* ===== roundtrip_ok: AddressT ===== *)

Theorem roundtrip_ok_address:
  ∀bs. LENGTH bs = 20 ⇒ roundtrip_ok (BaseTV AddressT) (BytesV (Fixed 20) bs)
Proof
  rw[] >> irule decode_value_single_slot >> simp[] >>
  qexists_tac `word_of_bytes_be (PAD_LEFT 0w 32 bs)` >>
  simp[encode_base_to_slot_def, decode_base_from_slot_def] >>
  DEP_REWRITE_TAC[word_to_bytes_be_word_of_bytes_be] >>
  simp[length_pad_left, PAD_LEFT, DROP_APPEND, LENGTH_GENLIST]
QED

(* ===== roundtrip_ok: BytesT (Fixed n) ===== *)

Theorem roundtrip_ok_fixed_bytes:
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

Theorem roundtrip_ok_uint:
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

Theorem roundtrip_ok_int:
  ∀n i. INT_MIN(:256) ≤ i ∧ i ≤ INT_MAX(:256) ⇒
    roundtrip_ok (BaseTV (IntT n)) (IntV (Signed n) i)
Proof
  rw[] >> irule decode_value_single_slot >> simp[] >>
  qexists_tac `i2w i` >>
  simp[encode_base_to_slot_def, decode_base_from_slot_def] >>
  simp[integer_wordTheory.w2i_i2w]
QED

(* ===== roundtrip_ok: DecimalT ===== *)

Theorem roundtrip_ok_decimal:
  ∀i. INT_MIN(:256) ≤ i ∧ i ≤ INT_MAX(:256) ⇒
    roundtrip_ok (BaseTV DecimalT) (DecimalV i)
Proof
  rw[] >> irule decode_value_single_slot >> simp[] >>
  qexists_tac `i2w i` >>
  simp[encode_base_to_slot_def, decode_base_from_slot_def] >>
  simp[integer_wordTheory.w2i_i2w]
QED

(* ===== roundtrip_ok: FlagTV ===== *)

Theorem roundtrip_ok_flag:
  ∀m k. k < dimword(:256) ⇒
    roundtrip_ok (FlagTV m) (FlagV m k)
Proof
  rw[roundtrip_ok_def] >>
  gvs[encode_value_def, AllCaseEqs()] >>
  gvs[decode_value_def, read_slot_after_apply_writes_single,
      decode_base_from_slot_def, encode_base_to_slot_def]
QED

(* ===== roundtrip_ok: NoneTV ===== *)

Theorem roundtrip_ok_none:
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
Theorem read_slots_eq_EL:
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

Theorem LENGTH_bytes_to_slots:
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
  simp[indexedListsTheory.MEM_MAPi] >>
  qexists_tac `i` >> simp[]
QED

(* Bounds compatibility: value bounds match type bounds *)
Definition bounds_compat_def:
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
Theorem encode_dyn_bytes_roundtrip:
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
Theorem roundtrip_ok_dyn_bytes:
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
Theorem roundtrip_ok_string:
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

(* ===== well_formed_value ===== *)

(* Termination helpers for well_formed_value *)
Theorem wf_struct_size_helper[local]:
  ∀fields : (identifier # value) list.
    list_size (pair_size (K 0) value_size) fields ≤
    list_size (pair_size (list_size char_size) value_size) fields
Proof
  Induct >> rw[] >> PairCases_on `h` >> rw[]
QED

Theorem wf_sparse_size_helper[local]:
  ∀sparse : (num # value) list.
    list_size (pair_size (K 0) value_size) sparse ≤
    list_size (pair_size I value_size) sparse
Proof
  Induct >> rw[] >> PairCases_on `h` >> rw[]
QED

(* Well-formedness predicate on values (no type needed).
   Checks: numeric range fits in 256-bit words,
           static array keys in range and non-default,
           dynamic array length within bound,
           recursive well-formedness of sub-values. *)
Definition well_formed_value_def:
  well_formed_value (IntV (Unsigned _) i) = (0 ≤ i ∧ i < &dimword(:256)) ∧
  well_formed_value (IntV (Signed _) i) = (INT_MIN(:256) ≤ i ∧ i ≤ INT_MAX(:256)) ∧
  well_formed_value (DecimalV i) = (INT_MIN(:256) ≤ i ∧ i ≤ INT_MAX(:256)) ∧
  well_formed_value (FlagV _ k) = (k < dimword(:256)) ∧
  well_formed_value (BoolV _) = T ∧
  well_formed_value NoneV = T ∧
  well_formed_value (BytesV _ _) = T ∧
  well_formed_value (StringV _ _) = T ∧
  well_formed_value (ArrayV av) = wf_array av ∧
  well_formed_value (StructV fields) = wf_fields fields ∧
  wf_array (TupleV vs) = wf_values vs ∧
  wf_array (SArrayV tv n sparse) =
    (SORTED $< (MAP FST sparse) ∧ wf_sparse tv n sparse) ∧
  wf_array (DynArrayV tv max vs) = (LENGTH vs ≤ max ∧ wf_values vs) ∧
  wf_values [] = T ∧
  wf_values (v::vs) = (well_formed_value v ∧ wf_values vs) ∧
  wf_sparse tv n [] = T ∧
  wf_sparse tv n ((k,v)::rest) =
    (k < n ∧ v ≠ default_value tv ∧ well_formed_value v ∧ wf_sparse tv n rest) ∧
  wf_fields [] = T ∧
  wf_fields ((name,v)::rest) = (well_formed_value v ∧ wf_fields rest)
Termination
  WF_REL_TAC `measure (λx. case x of
    | INL v => value_size v
    | INR (INL av) => array_value_size av
    | INR (INR (INL vs)) => list_size value_size vs
    | INR (INR (INR (INL (_, _, sparse)))) =>
        list_size value_size (MAP SND sparse)
    | INR (INR (INR (INR fields))) =>
        list_size value_size (MAP SND fields))` >>
  rw[vyperMiscTheory.list_size_pair_size_map]
End

(* ===== General roundtrip_ok from well_formed_value ===== *)

(* For non-compound types, roundtrip_ok follows from well_formed_value
   and IS_SOME (encode_value tv v) *)
Theorem roundtrip_ok_from_well_formed_base:
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
