(*
 * Value Encoding Proofs
 *
 * Proves theorems exported by valueEncodingPropsScript.
 *)

Theory valueEncodingProofs
Ancestors
  list rich_list venomMemProofs
  valueEncoding vyperStorage venomState
Libs
  blastLib intLib

(* ===== word_of_bytes helpers ===== *)

(* Appending zero bytes doesn't change word_of_bytes *)
Theorem word_of_bytes_replicate_zero:
  ∀ be (a : α word) n.
    word_of_bytes be a (REPLICATE n (0w : byte)) = (0w : α word)
Proof
  Induct_on `n` >>
  simp[byteTheory.word_of_bytes_def, rich_listTheory.REPLICATE,
       byteTheory.set_byte_def, byteTheory.word_slice_alt_zero,
       wordsTheory.w2w_0, wordsTheory.WORD_OR_CLAUSES,
       wordsTheory.ZERO_SHIFT]
QED

Theorem word_of_bytes_append_zero:
  ∀ be (a : α word) l n.
    word_of_bytes be a (l ++ REPLICATE n (0w : byte)) =
    word_of_bytes be a l
Proof
  Induct_on `l` >>
  simp[byteTheory.word_of_bytes_def, word_of_bytes_replicate_zero]
QED

Theorem word_of_bytes_be_pad_right:
  ∀ (l : byte list).
    word_of_bytes_be (PAD_RIGHT 0w 32 l) = word_of_bytes_be l
Proof
  simp[byteTheory.word_of_bytes_be_def, listTheory.PAD_RIGHT,
       GSYM rich_listTheory.REPLICATE_GENLIST, word_of_bytes_append_zero]
QED

(* ===== val_to_w256 agrees with encode_base_to_slot ===== *)

(* NOTE: val_to_w256 special-cases LENGTH bs = 20 with PAD_LEFT (address convention)
   but encode_base_to_slot for BytesT (Fixed n) uses unpadded encoding.
   These disagree when a 20-byte value is stored as bytesN (not address).
   The precondition excludes all BytesV + BytesT combinations. *)
Theorem val_to_w256_encode_agree_proof:
  ∀ v tv w.
    encode_base_to_slot v tv = SOME w ∧
    (* Exclude BytesV with BytesT — use AddressT instead *)
    (∀ bs n. v = BytesV bs ∧ tv = BaseTV (BytesT (Fixed n)) ⇒ F)
    ⇒
    val_to_w256 v = w
Proof
  Cases_on `v` >> Cases_on `tv` >>
  simp[encode_base_to_slot_def, val_to_w256_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  (* BoolV: split base_type then bool *)
  TRY (Cases_on `b'` >>
       gvs[encode_base_to_slot_def, bool_to_slot_def, AllCaseEqs()] >>
       Cases_on `b` >> gvs[] >> NO_TAC) >>
  (* IntV, DecimalV, BytesV: split base_type, then bound for BytesT *)
  Cases_on `b` >> gvs[encode_base_to_slot_def, AllCaseEqs()] >>
  Cases_on `b'` >> gvs[encode_base_to_slot_def, AllCaseEqs()]
QED

(* ===== Roundtrip ===== *)

(* Helper: bool roundtrip *)
Theorem bool_roundtrip:
  ∀ b. slot_to_bool (bool_to_slot b) = b
Proof
  Cases >> simp[bool_to_slot_def, slot_to_bool_def]
QED

(* Helper: EL i of word_to_bytes_be (word_of_bytes_be bs) = EL i bs
   when i < LENGTH bs ≤ 32 *)
(* Helper: TAKE n (word_to_bytes_be (word_of_bytes_be bs)) = bs
   when LENGTH bs = n ≤ 32 *)

val dimindex_256 = fcpLib.INDEX_CONV ``dimindex(:256)``;

Theorem TAKE_word_to_bytes_be_word_of_bytes_be:
  ∀ (bs : byte list).
    LENGTH bs ≤ 32 ⇒
    TAKE (LENGTH bs) (word_to_bytes_be (word_of_bytes_be bs : bytes32)) = bs
Proof
  rpt strip_tac >>
  irule listTheory.LIST_EQ >>
  simp[listTheory.EL_TAKE, byteTheory.word_to_bytes_be_def,
       byteTheory.word_to_bytes_def, byteTheory.LENGTH_word_to_bytes_aux,
       dimindex_256] >>
  rpt strip_tac >>
  simp[listTheory.EL_TAKE] >>
  `x < 32` by simp[] >>
  simp[dimindex_256, byteTheory.EL_word_to_bytes_aux] >>
  simp[byteTheory.word_of_bytes_be_def] >>
  simp[dimindex_256, byteTheory.get_byte_word_of_bytes_be] >>
  simp[byteTheory.first_byte_at_0w, wordsTheory.dimword_def, dimindex_256]
QED

(* Full roundtrip needs well-typedness — values must fit in word.
   For Phase 1, we only need BoolV, unsigned ints with i < 2^256,
   and signed ints with -2^255 ≤ i < 2^255. *)
(* Helper: word_to_bytes_be roundtrip for PAD_LEFT address encoding *)
Theorem word_to_bytes_be_pad_left_roundtrip:
  ∀ (l : byte list).
    LENGTH l = 20 ⇒
    DROP 12 (word_to_bytes_be (word_of_bytes_be (PAD_LEFT 0w 32 l) : bytes32)) = l
Proof
  rpt strip_tac
  >> `word_to_bytes_be (word_of_bytes_be (PAD_LEFT 0w 32 l) : bytes32) =
      PAD_LEFT 0w 32 l` by (
    irule listTheory.LIST_EQ
    >> simp[byteTheory.word_to_bytes_be_def, byteTheory.word_to_bytes_def,
            byteTheory.LENGTH_word_to_bytes_aux, dimindex_256,
            bitstringTheory.length_pad_left]
    >> rpt strip_tac
    >> `x < 32` by simp[]
    >> simp[dimindex_256, byteTheory.EL_word_to_bytes_aux,
            byteTheory.word_of_bytes_be_def,
            byteTheory.get_byte_word_of_bytes_be]
    >> simp[byteTheory.first_byte_at_0w, wordsTheory.dimword_def,
            dimindex_256, bitstringTheory.length_pad_left])
  >> gvs[listTheory.PAD_LEFT, GSYM rich_listTheory.REPLICATE_GENLIST,
         rich_listTheory.DROP_APPEND1, rich_listTheory.DROP_REPLICATE]
QED

(* Helper: truncate_unsigned roundtrips for nat values in range *)
Theorem truncate_unsigned_n2w_roundtrip:
  !n (k:num). k < 2 ** n /\ n <= 256 ==>
    truncate_unsigned n ((n2w k) : bytes32) = k
Proof
  PURE_REWRITE_TAC[truncate_unsigned_def, wordsTheory.w2n_n2w] >>
  rpt strip_tac >>
  `k MOD dimword(:256) = k` by
    (irule arithmeticTheory.LESS_MOD >>
     simp[wordsTheory.dimword_def] >>
     irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `2 ** n` >> simp[]) >>
  simp[]
QED

(* Helper: truncate_unsigned roundtrips for int values via i2w *)
Theorem truncate_unsigned_i2w_roundtrip:
  !n (i:int). 0 <= i /\ i < &(2 ** n) /\ n <= 256 ==>
    &(truncate_unsigned n ((i2w i) : bytes32)) = i
Proof
  PURE_REWRITE_TAC[truncate_unsigned_def] >> rpt strip_tac >>
  `2 ** n <= dimword(:256)` by simp[wordsTheory.dimword_def] >>
  `0 <= i /\ i < &dimword(:256)` by intLib.ARITH_TAC >>
  `i % &dimword(:256) = i` by simp[integerTheory.INT_LESS_MOD] >>
  `&(w2n ((i2w i) : bytes32)) = i` by
    simp[integer_wordTheory.w2n_i2w] >>
  `w2n ((i2w i) : bytes32) = Num i` by intLib.ARITH_TAC >>
  `Num i < 2 ** n` by intLib.ARITH_TAC >>
  simp[]
QED

(* ===== truncate_signed roundtrip helpers ===== *)

Theorem dimword_256_exp[local]:
  dimword(:256) = 2 ** 256
Proof
  simp[wordsTheory.dimword_def]
QED

Theorem w2n_i2w_nonneg[local]:
  !i. 0 <= i /\ Num i < dimword(:256) ==>
    w2n ((i2w i):256 word) = Num i
Proof
  rpt strip_tac >>
  `&(w2n ((i2w i):256 word)) = i % &(dimword(:256))` by
    simp[integer_wordTheory.w2n_i2w] >>
  `i < &(dimword(:256))` by intLib.ARITH_TAC >>
  `i % &(dimword(:256)) = i` by simp[integerTheory.INT_LESS_MOD] >>
  `i = &(Num i)` by simp[integerTheory.INT_OF_NUM] >>
  intLib.ARITH_TAC
QED

Theorem w2n_i2w_neg[local]:
  !i. i < 0 /\ -&(dimword(:256)) < i ==>
    w2n ((i2w i):256 word) = Num (i + &(dimword(:256)))
Proof
  rpt strip_tac >>
  `&(w2n ((i2w i):256 word)) = i % &(dimword(:256))` by
    simp[integer_wordTheory.w2n_i2w] >>
  `0 < dimword(:256)` by simp[wordsTheory.ZERO_LT_dimword] >>
  `&(dimword(:256)) <> (0:int)` by intLib.ARITH_TAC >>
  `0 <= i + &(dimword(:256)) /\ i + &(dimword(:256)) < &(dimword(:256))` by
    intLib.ARITH_TAC >>
  `(i + &(dimword(:256))) % &(dimword(:256)) = i + &(dimword(:256))` by
    simp[integerTheory.INT_LESS_MOD] >>
  `(-1 * &(dimword(:256)) + (i + &(dimword(:256)))) % &(dimword(:256)) =
   (i + &(dimword(:256))) % &(dimword(:256))` by
    simp[integerTheory.INT_MOD_ADD_MULTIPLES] >>
  `-1 * &(dimword(:256)) + (i + &(dimword(:256))) = i` by intLib.ARITH_TAC >>
  `0 <= i + &(dimword(:256))` by intLib.ARITH_TAC >>
  `&(w2n ((i2w i):256 word)) = i + &(dimword(:256))` by metis_tac[] >>
  metis_tac[integerTheory.NUM_OF_INT, integerTheory.INT_INJ]
QED

Theorem dimword_sub_mod[local]:
  !n (k:num). 0 < k /\ k <= 2 ** (n-1) /\ 0 < n /\ n <= 256 ==>
    (dimword(:256) - k) MOD 2 ** n = 2 ** n - k
Proof
  rpt strip_tac >>
  `k < 2 ** n` by
    (irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
     qexists_tac `2 ** (n-1)` >> simp[] >>
     `n - 1 < n` by simp[] >> simp[]) >>
  `0 < 2 ** n` by simp[] >>
  `0 < 2 ** (256 - n)` by simp[] >>
  `k < 2 ** (256 - n) * 2 ** n` by
    (irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `2 ** n` >> simp[] >>
     `1 <= 2 ** (256 - n)` by simp[] >> simp[]) >>
  `dimword(:256) = 2 ** (256 - n) * 2 ** n` by
    (REWRITE_TAC[dimword_256_exp, GSYM arithmeticTheory.EXP_ADD] >>
     AP_TERM_TAC >> simp[]) >>
  pop_assum (fn eq => REWRITE_TAC[eq]) >>
  mp_tac (Q.SPECL [`2 ** n`, `2 ** (256 - n)`, `k`]
    wordsTheory.MOD_COMPLEMENT) >>
  impl_tac >- simp[] >>
  `k MOD 2 ** n = k` by simp[arithmeticTheory.LESS_MOD] >>
  `2 ** n - k < 2 ** n` by simp[] >>
  disch_then (fn th => REWRITE_TAC[th]) >>
  simp[arithmeticTheory.LESS_MOD]
QED

(* Helper: truncate_signed roundtrips for values in signed range *)
Theorem truncate_signed_i2w_roundtrip:
  !n (i:int). 0 < n /\ n <= 256 /\
    -&(2 ** (n - 1)) <= i /\ i < &(2 ** (n - 1)) ==>
    truncate_signed n ((i2w i) : bytes32) = i
Proof
  rpt strip_tac >>
  `?m. n = SUC m` by (Cases_on `n` >> fs[]) >> gvs[] >>
  `m <= 255` by simp[] >>
  Cases_on `i < 0` >> gvs[]
  (* Negative case *)
  >- (
    `0 <= -i` by intLib.ARITH_TAC >>
    `0 < Num(-i)` by intLib.ARITH_TAC >>
    `Num(-i) <= 2 ** m` by intLib.ARITH_TAC >>
    (* Derive -&dimword < i via nat→int lifting *)
    `Num(-i) < dimword(:256)` by
      (REWRITE_TAC[dimword_256_exp] >>
       irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
       qexists_tac `2 ** m` >> simp[]) >>
    `&(Num(-i)) < &(dimword(:256))` by
      simp[integerTheory.INT_LT] >>
    `-i = &(Num(-i))` by simp[integerTheory.INT_OF_NUM] >>
    `-&(dimword(:256)) < i` by intLib.ARITH_TAC >>
    (* Compute w2n(i2w i) *)
    `w2n ((i2w i):256 word) = Num (i + &(dimword(:256)))` by
      (irule w2n_i2w_neg >> simp[]) >>
    `i = -&(Num(-i))` by intLib.ARITH_TAC >>
    `Num(i + &(dimword(:256))) = dimword(:256) - Num(-i)` by
      (`i + &(dimword(:256)) = &(dimword(:256) - Num(-i))` by
         intLib.ARITH_TAC >>
       pop_assum (fn th => REWRITE_TAC[th]) >>
       simp[integerTheory.NUM_OF_INT]) >>
    `w2n ((i2w i):256 word) = dimword(:256) - Num(-i)` by
      metis_tac[] >>
    (* Unfold truncate_signed and rewrite w2n *)
    CONV_TAC (RATOR_CONV (RAND_CONV
      (PURE_REWRITE_CONV [truncate_signed_def, LET_THM]
       THENC DEPTH_CONV BETA_CONV))) >>
    qpat_x_assum `w2n _ = dimword _ - _` (fn th => REWRITE_TAC[th]) >>
    `(dimword(:256) - Num(-i)) MOD 2 ** SUC m = 2 ** SUC m - Num(-i)` by
      (irule dimword_sub_mod >> simp[]) >>
    pop_assum (fn th => REWRITE_TAC[th]) >>
    `SUC m - 1 = m` by simp[] >>
    pop_assum (fn th => REWRITE_TAC[th]) >>
    `Num(-i) <= 2 ** SUC m` by simp[arithmeticTheory.EXP] >>
    `~(2 ** SUC m - Num(-i) < 2 ** m)` by simp[arithmeticTheory.EXP] >>
    ASM_SIMP_TAC bool_ss [] >>
    REWRITE_TAC[GSYM (Q.SPECL [`2 ** SUC m`, `Num(-i)`]
      integerTheory.INT_SUB |> UNDISCH)] >>
    intLib.ARITH_TAC)
  (* Non-negative case *)
  >> (
    `0 <= i` by intLib.ARITH_TAC >>
    `Num i < 2 ** m` by intLib.ARITH_TAC >>
    `Num i < dimword(:256)` by
      (REWRITE_TAC[dimword_256_exp] >>
       irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
       qexists_tac `2 ** m` >> simp[]) >>
    `w2n ((i2w i):256 word) = Num i` by
      (irule w2n_i2w_nonneg >> simp[]) >>
    simp[truncate_signed_def] >>
    `Num i < 2 ** SUC m` by simp[arithmeticTheory.EXP] >>
    simp[integerTheory.INT_OF_NUM])
QED

(* w256_roundtrip: encode then decode is identity.
   Preconditions require per-type bounds (n-bit range, not 256-bit)
   because decode_base_from_slot truncates to the declared type's range. *)
Theorem w256_roundtrip_proof:
  ∀ v tv w.
    encode_base_to_slot v tv = SOME w ∧
    (∀ i n. v = IntV i ∧ tv = BaseTV (UintT n) ⇒
            0 ≤ i ∧ i < &(2 ** n) ∧ n ≤ 256) ∧
    (∀ i n. v = IntV i ∧ tv = BaseTV (IntT n) ⇒
            0 < n ∧ n ≤ 256 ∧
            -&(2 ** (n - 1)) ≤ i ∧ i < &(2 ** (n - 1))) ∧
    (∀ k m. v = FlagV k ∧ tv = FlagTV m ⇒ k < 2 ** m ∧ m ≤ 256) ∧
    (∀ n. v = DecimalV n ⇒ -&(2 ** 167) ≤ n ∧ n < &(2 ** 167))
    ⇒
    w256_to_val w tv = v
Proof
  Cases_on `v` >> Cases_on `tv` >>
  simp[encode_base_to_slot_def, w256_to_val_def,
       decode_base_from_slot_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  (* 0: BoolV + BaseTV *)
  >- (Cases_on `b'` >> Cases_on `b` >>
      gvs[encode_base_to_slot_def, decode_base_from_slot_def,
          bool_to_slot_def, slot_to_bool_def, AllCaseEqs()])
  (* 1: IntV + BaseTV *)
  >- (rename1 `encode_base_to_slot _ (BaseTV bt) = SOME _` >>
      Cases_on `bt` >>
      gvs[encode_base_to_slot_def, decode_base_from_slot_def, AllCaseEqs()]
      (* UintT *)
      >- simp[truncate_unsigned_i2w_roundtrip]
      (* IntT *)
      >> simp[truncate_signed_i2w_roundtrip])
  (* 2: FlagV + FlagTV *)
  >- simp[truncate_unsigned_n2w_roundtrip]
  (* 3: DecimalV + BaseTV *)
  >- (Cases_on `b` >> gvs[encode_base_to_slot_def, decode_base_from_slot_def,
         AllCaseEqs()] >>
      irule truncate_signed_i2w_roundtrip >> simp[])
  (* 4: BytesV + BaseTV *)
  >> (Cases_on `b` >> TRY (Cases_on `b'`) >>
      gvs[encode_base_to_slot_def, decode_base_from_slot_def,
          AllCaseEqs(), TAKE_word_to_bytes_be_word_of_bytes_be,
          word_to_bytes_be_pad_left_roundtrip])
QED

(* ===== mem_word_at = mload ===== *)

Theorem mem_word_at_eq_mload_proof:
  ∀ offset s.
    mem_word_at offset s.vs_memory = mload offset s
Proof
  rw[mem_word_at_def, mload_def]
QED

Theorem LENGTH_mem_bytes_at_proof:
  ∀ offset len mem. LENGTH (mem_bytes_at offset len mem) = len
Proof
  rw[mem_bytes_at_def, LENGTH_TAKE_EQ, LENGTH_DROP, LENGTH_APPEND,
     LENGTH_REPLICATE]
QED

Theorem mload_eq_mem_bytes_at_eq_proof:
  ∀ off1 off2 s1 s2.
    mload off1 s1 = mload off2 s2 ⇒
    mem_bytes_at off1 32 s1.vs_memory =
    mem_bytes_at off2 32 s2.vs_memory
Proof
  rw[mload_def, mem_bytes_at_def] >>
  irule (INST_TYPE[alpha |-> ``:256``] word_of_bytes_be_inj_proof) >>
  simp[dividesTheory.divides_def]
QED

(* ===== Primitive val_in_memory ===== *)

Theorem val_in_memory_prim_proof:
  ∀ v offset mem ty.
    (∃ b. v = BoolV b) ∨ (∃ n. v = IntV n) ∨
    (∃ k. v = FlagV k) ∨ (∃ n. v = DecimalV n) ⇒
    (val_in_memory ty v offset mem ⇔
      mem_word_at offset mem = val_to_w256 v)
Proof
  rpt strip_tac >> gvs[val_in_memory_def]
QED

(* ===== Address encoding ===== *)

(* word_to_bytes of a zero-extended address = PAD_LEFT of address bytes *)
Theorem word_to_bytes_w2w_address:
  word_to_bytes (w2w (a:address) : bytes32) T =
    PAD_LEFT (0w:word8) 32 (word_to_bytes (a:address) T)
Proof
  simp[byteTheory.word_to_bytes_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``,
       fcpLib.INDEX_CONV ``dimindex(:160)``]
  >> simp[listTheory.PAD_LEFT, byteTheory.LENGTH_word_to_bytes_aux]
  >> simp[byteTheory.word_to_bytes_aux_compute]
  >> simp[byteTheory.get_byte_def, byteTheory.byte_index_def,
          fcpLib.INDEX_CONV ``dimindex(:256)``,
          fcpLib.INDEX_CONV ``dimindex(:160)``]
  >> BBLAST_TAC
QED

(* val_to_w256 for addresses equals w2w (zero extension) *)
Theorem val_to_w256_address:
  val_to_w256 (AddressV a) = w2w a
Proof
  simp[val_to_w256_def]
  >> `PAD_LEFT (0w:word8) 32 (word_to_bytes (a:address) T) =
      word_to_bytes (w2w a : bytes32) T`
       by simp[word_to_bytes_w2w_address]
  >> pop_assum SUBST1_TAC
  >> simp[byteTheory.word_of_bytes_be_def,
          vfmTypesTheory.word_to_bytes_word_of_bytes_256]
QED

(* ===== Layer 1: mstore / mem_word_at interaction ===== *)

(* mstore at offset, then read mem_word_at same offset, gets original word back.
   Core fact: word_of_bytes T 0w (word_to_bytes w T) = w
   (vfmTypesTheory.word_to_bytes_word_of_bytes_256).
   The byte-list surgery is: mstore writes TAKE off expanded ++ word_to_bytes w T ++ DROP (off+32) expanded,
   then mem_word_at reads TAKE 32 (DROP off result ++ REPLICATE 32 0w).
   Need to show DROP off (TAKE off X ++ bytes ++ tail) = bytes ++ tail,
   then TAKE 32 (bytes ++ ...) = bytes when LENGTH bytes = 32.
   See lowerDloadProofsScript.sml:write_then_mload for a similar local proof. *)
Theorem drop_take_append[local]:
  ∀ off (xs : α list) ys.
    off ≤ LENGTH xs ⇒ DROP off (TAKE off xs ++ ys) = ys
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[listTheory.DROP_APPEND] >>
  REWRITE_TAC[rich_listTheory.DROP_TAKE_EQ_NIL] >>
  simp[listTheory.LENGTH_TAKE]
QED

Theorem LENGTH_word_to_bytes_256[local,simp]:
  LENGTH (word_to_bytes (w:bytes32) T) = 32
Proof
  simp[byteTheory.LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

(* ===== Core splice/expansion helpers ===== *)

(* mstore = write_memory_with_expansion on word_to_bytes *)
Theorem mstore_eq_wmwe:
  ∀ off (w:bytes32) s.
    mstore off w s = write_memory_with_expansion off (word_to_bytes w T) s
Proof
  simp[mstore_def, write_memory_with_expansion_def, LET_THM]
QED

(* TAKE k (xs ++ REPLICATE m c) only depends on the first k elements:
   extra padding beyond k is irrelevant. *)
Theorem TAKE_append_REPLICATE:
  ∀ k (xs : α list) m n (c : α).
    k ≤ LENGTH xs + m ∧ k ≤ LENGTH xs + n ⇒
    TAKE k (xs ++ REPLICATE m c) = TAKE k (xs ++ REPLICATE n c)
Proof
  rpt strip_tac >> irule listTheory.LIST_EQ >>
  simp[listTheory.LENGTH_TAKE_EQ, listTheory.EL_TAKE,
       listTheory.EL_APPEND_EQN, rich_listTheory.EL_REPLICATE]
QED

(* Appending zero-bytes is invisible to mem_word_at, because
   mem_word_at already zero-pads via REPLICATE 32 0w. *)
(* Merge REPLICATE padding after DROP *)
Theorem drop_append_replicate_merge:
  ∀ off (mem : α list) n k (c : α).
    DROP off (mem ++ REPLICATE n c) ++ REPLICATE k c =
    DROP off mem ++ REPLICATE (n − (off − LENGTH mem) + k) c
Proof
  rpt gen_tac >>
  REWRITE_TAC[listTheory.DROP_APPEND] >>
  simp[rich_listTheory.DROP_REPLICATE,
       GSYM listTheory.APPEND_ASSOC,
       rich_listTheory.REPLICATE_APPEND]
QED

Theorem mem_word_at_append_zero:
  ∀ off mem n.
    mem_word_at off (mem ++ REPLICATE n (0w:byte)) = mem_word_at off mem
Proof
  rpt gen_tac >> simp[mem_word_at_def] >>
  AP_TERM_TAC >>
  REWRITE_TAC[drop_append_replicate_merge] >>
  irule TAKE_append_REPLICATE >> simp[]
QED

(* Same for mem_bytes_at *)
Theorem mem_bytes_at_append_zero:
  ∀ off len mem n.
    mem_bytes_at off len (mem ++ REPLICATE n (0w:byte)) =
    mem_bytes_at off len mem
Proof
  rpt gen_tac >> simp[mem_bytes_at_def] >>
  REWRITE_TAC[drop_append_replicate_merge] >>
  irule TAKE_append_REPLICATE >> simp[]
QED

(* Reading n bytes from a splice at a disjoint offset returns
   the same as reading from the unspliced list.
   splice = TAKE off2 xs ++ bs ++ DROP (off2 + LENGTH bs) xs *)
Theorem take_drop_splice_disjoint:
  ∀ off1 n off2 (bs : α list) (xs : α list) (pad : α list).
    off2 + LENGTH bs ≤ LENGTH xs ∧
    (off1 + n ≤ off2 ∨ off2 + LENGTH bs ≤ off1) ⇒
    TAKE n (DROP off1
      (TAKE off2 xs ++ bs ++ DROP (off2 + LENGTH bs) xs) ++ pad) =
    TAKE n (DROP off1 xs ++ pad)
Proof
  rpt strip_tac >>
  irule listTheory.LIST_EQ >>
  simp[listTheory.LENGTH_TAKE_EQ, listTheory.EL_TAKE,
       listTheory.EL_APPEND_EQN, listTheory.EL_DROP,
       listTheory.LENGTH_DROP]
QED

Theorem mstore_mem_word_at_same_proof:
  ∀ off (w:bytes32) s.
    mem_word_at off (mstore off w s).vs_memory = w
Proof
  rpt strip_tac >>
  simp[mstore_eq_wmwe, mem_word_at_def,
       write_memory_with_expansion_def, LET_THM] >>
  qabbrev_tac `mem = s.vs_memory` >>
  Cases_on `0 < off + 32 - LENGTH mem`
  >- (simp[] >>
      qabbrev_tac `expanded = mem ++ REPLICATE (off + 32 - LENGTH mem) 0w` >>
      `LENGTH expanded = off + 32` by
        (simp[Abbr `expanded`]) >>
      `off ≤ LENGTH expanded` by simp[] >>
      `DROP (off + 32) expanded = []` by
        metis_tac[rich_listTheory.DROP_LENGTH_NIL] >>
      simp[] >>
      `DROP off (TAKE off expanded ++ word_to_bytes w T) =
       word_to_bytes w T` by
        (irule drop_take_append >> simp[]) >>
      simp[listTheory.TAKE_APPEND1, listTheory.TAKE_LENGTH_ID_rwt,
           vfmTypesTheory.word_to_bytes_word_of_bytes_256])
  >- (simp[] >>
      `off + 32 ≤ LENGTH mem` by simp[] >>
      `off ≤ LENGTH mem` by simp[] >>
      ONCE_REWRITE_TAC[GSYM listTheory.APPEND_ASSOC] >>
      `DROP off (TAKE off mem ++
         (word_to_bytes w T ++ DROP (off + 32) mem)) =
       word_to_bytes w T ++ DROP (off + 32) mem` by
        (irule drop_take_append >> simp[]) >>
      simp[listTheory.TAKE_APPEND1, listTheory.TAKE_LENGTH_ID_rwt,
           vfmTypesTheory.word_to_bytes_word_of_bytes_256])
QED

(* mstore at off2 preserves mem_word_at at off1 when regions don't overlap.
   Regions are [off1, off1+32) and [off2, off2+32). *)
(* Shared tactic for disjoint read proofs: unfold mstore, case split on
   expansion, apply splice disjoint in each case, clean up expansion. *)
(* Shared proof structure for disjoint mem_word_at / mem_bytes_at.
   Strategy: unfold mstore to splice, apply take_drop_splice_disjoint,
   then use mem_word/bytes_at_append_zero for expansion case. *)
(* Helper tactic pattern: rewrite DROP (off + 32) to DROP (off + LENGTH (word_to_bytes w T))
   so irule take_drop_splice_disjoint can match *)
Theorem splice_disjoint_word:
  ∀ off1 n off2 (w : bytes32) (xs : byte list) (pad : byte list).
    off2 + 32 ≤ LENGTH xs ∧
    (off1 + n ≤ off2 ∨ off2 + 32 ≤ off1) ⇒
    TAKE n (DROP off1
      (TAKE off2 xs ++ word_to_bytes w T ++ DROP (off2 + 32) xs) ++ pad) =
    TAKE n (DROP off1 xs ++ pad)
Proof
  rpt strip_tac >>
  `32 = LENGTH (word_to_bytes w T)` by simp[] >>
  pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
  irule take_drop_splice_disjoint >> simp[]
QED

Theorem mstore_mem_word_at_disjoint_proof:
  ∀ off1 off2 (w:bytes32) s.
    (off1 + 32 ≤ off2 ∨ off2 + 32 ≤ off1) ⇒
    mem_word_at off1 (mstore off2 w s).vs_memory =
    mem_word_at off1 s.vs_memory
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp[mstore_eq_wmwe, write_memory_with_expansion_def, LET_THM] >>
  Cases_on `0 < off2 + 32 - LENGTH s.vs_memory` >> simp[]
  >- (qmatch_goalsub_abbrev_tac `TAKE off2 exp` >>
      `off2 + 32 ≤ LENGTH exp` by simp[Abbr `exp`] >>
      `mem_word_at off1 (TAKE off2 exp ++ word_to_bytes w T ++
        DROP (off2 + 32) exp) = mem_word_at off1 exp` by (
        simp[mem_word_at_def] >> AP_TERM_TAC >>
        irule splice_disjoint_word >> simp[]) >>
      simp[Abbr `exp`, mem_word_at_append_zero])
  >- (`off2 + 32 ≤ LENGTH s.vs_memory` by simp[] >>
      simp[mem_word_at_def] >> AP_TERM_TAC >>
      irule splice_disjoint_word >> simp[])
QED

Theorem mstore_mem_bytes_at_disjoint_proof:
  ∀ off1 len off2 (w:bytes32) s.
    (off1 + len ≤ off2 ∨ off2 + 32 ≤ off1) ⇒
    mem_bytes_at off1 len (mstore off2 w s).vs_memory =
    mem_bytes_at off1 len s.vs_memory
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp[mstore_eq_wmwe, write_memory_with_expansion_def, LET_THM] >>
  Cases_on `0 < off2 + 32 - LENGTH s.vs_memory` >> simp[]
  >- (qmatch_goalsub_abbrev_tac `TAKE off2 exp` >>
      `off2 + 32 ≤ LENGTH exp` by simp[Abbr `exp`] >>
      `mem_bytes_at off1 len (TAKE off2 exp ++ word_to_bytes w T ++
        DROP (off2 + 32) exp) = mem_bytes_at off1 len exp` by (
        simp[mem_bytes_at_def] >>
        irule splice_disjoint_word >> simp[]) >>
      simp[Abbr `exp`, mem_bytes_at_append_zero])
  >- (`off2 + 32 ≤ LENGTH s.vs_memory` by simp[] >>
      simp[mem_bytes_at_def] >>
      irule splice_disjoint_word >> simp[])
QED

(* mstore establishes val_in_memory for primitive (word-sized) values.
   The value must be one that val_in_memory checks via mem_word_at
   (BoolV, IntV, FlagV, DecimalV). *)
Theorem mstore_establishes_val_in_memory_prim_proof:
  ∀ off v s ty.
    ((∃ b. v = BoolV b) ∨ (∃ n. v = IntV n) ∨
     (∃ k. v = FlagV k) ∨ (∃ n. v = DecimalV n)) ⇒
    val_in_memory ty v off (mstore off (val_to_w256 v) s).vs_memory
Proof
  rpt strip_tac >> gvs[] >>
  simp[val_in_memory_def, mstore_mem_word_at_same_proof]
QED

(* NOTE: mstore_preserves_val_in_memory_prim was removed as redundant —
   subsumed by mstore_preserves_val_in_memory conjunct 1 + val_in_memory_prim. *)

(* ===== Layer 2: type_memory_size properties ===== *)

(* Primitive base types always occupy 32 bytes in memory.
   Excludes dynamic bytes and strings which have variable size. *)
Theorem type_memory_size_prim_proof:
  ∀ bt.
    (∀ n. bt ≠ BytesT (Dynamic n)) ∧
    (∀ n. bt ≠ StringT n) ⇒
    type_memory_size (BaseTV bt) = 32
Proof
  Cases >> simp[type_memory_size_def] >>
  Cases_on `b` >> simp[type_memory_size_def]
QED

(* FlagTV always 32 bytes *)
Theorem type_memory_size_flag_proof:
  ∀ name. type_memory_size (FlagTV name) = 32
Proof
  simp[type_memory_size_def]
QED

(* ===== Layer 2: val_in_memory compound disjointness ===== *)

(* Core disjointness theorem: writing 32 bytes outside the region
   [off, off + type_memory_size ty) preserves val_in_memory.

   Requires mutual induction on val_in_memory's recursive structure
   (val, fields, elems, kvs, tuple). Each leaf case reduces to
   mstore_mem_word_at_disjoint or mstore_mem_bytes_at_disjoint.
   The val_in_memory case dispatches on value constructor; for
   compound constructors (StructV, ArrayV, StringV, BytesV dynamic),
   the size bound propagates through type_memory_size arithmetic.

   The free variable s is scaffolding: mstore only reads s.vs_memory
   (overridden to mem), so the result is independent of other fields. *)
(* Helper: kvs_val_wf implies val_wf for each MEM element *)
Theorem kvs_val_wf_mem[local]:
  ∀ kvs tv bound k v.
    kvs_val_wf kvs tv bound ∧ MEM (k,v) kvs ⇒ val_wf tv v
Proof
  Induct >> simp[val_wf_def] >>
  Cases >> rpt gen_tac >> strip_tac >> gvs[val_wf_def] >>
  metis_tac[]
QED

(* Helper: kvs_val_wf implies k < bound for each MEM element *)
Theorem kvs_val_wf_bound[local]:
  ∀ kvs tv bound k v.
    kvs_val_wf kvs tv bound ∧ MEM (k,v) kvs ⇒ k < bound
Proof
  Induct >> simp[val_wf_def] >>
  Cases >> rpt gen_tac >> strip_tac >> gvs[val_wf_def] >>
  metis_tac[]
QED

Theorem mstore_preserves_val_in_memory_proof:
  (∀ ty v off mem off2 (w:bytes32).
    val_in_memory ty v off mem ∧ val_wf ty v ∧
    (off2 + 32 ≤ off ∨ off + type_memory_size ty ≤ off2) ⇒
    val_in_memory ty v off (mstore off2 w (s with vs_memory := mem)).vs_memory) ∧
  (∀ fields field_tvs off mem off2 (w:bytes32).
    fields_in_memory fields field_tvs off mem ∧
    fields_val_wf fields field_tvs ∧
    (off2 + 32 ≤ off ∨ off + type_memory_size_fields field_tvs ≤ off2) ⇒
    fields_in_memory fields field_tvs off
      (mstore off2 w (s with vs_memory := mem)).vs_memory) ∧
  (∀ vs off tv mem off2 (w:bytes32).
    elems_in_memory vs off tv mem ∧ elems_val_wf vs tv ∧
    (off2 + 32 ≤ off ∨
     off + LENGTH vs * type_memory_size tv ≤ off2) ⇒
    elems_in_memory vs off tv
      (mstore off2 w (s with vs_memory := mem)).vs_memory) ∧
  (∀ (kvs : (num # value) list) base_off tv mem off2 (w:bytes32).
    kvs_in_memory kvs base_off tv mem ∧
    (∀ k v. MEM (k,v) kvs ⇒ val_wf tv v) ∧
    (∀ k v. MEM (k,v) kvs ⇒
      off2 + 32 ≤ base_off + k * type_memory_size tv ∨
      base_off + k * type_memory_size tv + type_memory_size tv ≤ off2) ⇒
    kvs_in_memory kvs base_off tv
      (mstore off2 w (s with vs_memory := mem)).vs_memory) ∧
  (∀ vs tvs off mem off2 (w:bytes32).
    tuple_in_memory vs tvs off mem ∧ tuple_val_wf vs tvs ∧
    (off2 + 32 ≤ off ∨ off + type_memory_size_list tvs ≤ off2) ⇒
    tuple_in_memory vs tvs off
      (mstore off2 w (s with vs_memory := mem)).vs_memory)
Proof
  ho_match_mp_tac val_in_memory_ind >> rpt conj_tac
  (* 1-4: Primitives (BoolV, IntV, FlagV, DecimalV) + NoneV + base [] cases *)
  >> TRY (rpt gen_tac >> rpt strip_tac >>
          gvs[val_in_memory_def, val_wf_def] >>
          `off + 32 ≤ off2 ∨ off2 + 32 ≤ off` by DECIDE_TAC >>
          simp[mstore_mem_word_at_disjoint_proof] >> NO_TAC)
  >> TRY (simp[val_in_memory_def] >> NO_TAC)
  (* 5: BytesV — case split to resolve type, then use disjoint lemmas *)
  >- (rpt gen_tac >> rpt strip_tac >>
      Cases_on `ty` >>
      gvs[val_in_memory_def, val_wf_def, type_memory_size_def] >>
      TRY (rename1 `BaseTV bt` >> Cases_on `bt` >>
           gvs[val_in_memory_def, val_wf_def, type_memory_size_def] >>
           TRY (rename1 `BytesT bnd` >> Cases_on `bnd` >>
                gvs[val_in_memory_def, val_wf_def, type_memory_size_def])) >>
      `off + 32 ≤ off2 ∨ off2 + 32 ≤ off` by DECIDE_TAC >>
      TRY (`(off + 32) + LENGTH bs ≤ off2 ∨ off2 + 32 ≤ off + 32`
             by DECIDE_TAC) >>
      fs[mstore_mem_word_at_disjoint_proof, mstore_mem_bytes_at_disjoint_proof])
  (* 6: StringV *)
  >- (rpt gen_tac >> rpt strip_tac >>
      gvs[val_in_memory_def, val_wf_def] >>
      `off + 32 ≤ off2 ∨ off2 + 32 ≤ off` by DECIDE_TAC >>
      simp[mstore_mem_word_at_disjoint_proof, mstore_mem_bytes_at_disjoint_proof] >>
      gvs[])
  (* 8: StructV *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[val_in_memory_def, val_wf_def, AllCaseEqs(), type_memory_size_def] >>
      Cases_on `ty` >> gvs[] >>
      first_x_assum irule >> gvs[type_memory_size_def])
  (* 9: DynArrayV — fs splits disjunction, Cases_on gives t:type_value, b:bound *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> rpt strip_tac >>
      fs[val_wf_def] >>
      Cases_on `ty` >> fs[] >>
      Cases_on `b` >> fs[val_in_memory_def, type_memory_size_def] >>
      rpt conj_tac >>
      TRY (`off + 32 ≤ off2 ∨ off2 + 32 ≤ off` by DECIDE_TAC >>
           fs[mstore_mem_word_at_disjoint_proof] >> NO_TAC) >>
      first_x_assum irule >> simp[] >>
      `LENGTH vs * type_memory_size t ≤ n * type_memory_size t`
        suffices_by DECIDE_TAC >>
      simp[arithmeticTheory.LE_MULT_RCANCEL])
  (* 10: SArrayV *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> rpt strip_tac >>
      fs[val_wf_def] >>
      Cases_on `ty` >> fs[] >>
      Cases_on `b` >> fs[val_in_memory_def, type_memory_size_def] >>
      first_x_assum irule >>
      rpt conj_tac >> rpt strip_tac >>
      TRY (metis_tac[kvs_val_wf_mem] >> NO_TAC) >>
      drule_all kvs_val_wf_bound >> strip_tac >>
      `SUC k * type_memory_size t ≤ n * type_memory_size t`
        by simp[arithmeticTheory.LE_MULT_RCANCEL] >>
      `type_memory_size t + k * type_memory_size t =
       SUC k * type_memory_size t` by simp[arithmeticTheory.MULT] >>
      DECIDE_TAC)
  (* 11: TupleV *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> rpt strip_tac >>
      fs[val_wf_def] >>
      Cases_on `ty` >> fs[val_in_memory_def, type_memory_size_def] >>
      first_x_assum irule >> simp[])
  (* 13: fields cons *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> rpt strip_tac >>
      Cases_on `field_tvs` >> TRY (Cases_on `h`) >>
      gvs[val_in_memory_def, val_wf_def, LET_THM, AllCaseEqs(),
          type_memory_size_def] >>
      conj_tac >> first_x_assum irule >> simp[type_memory_size_def])
  (* 15: elems cons — simp[] leaves arithmetic from SUC(LENGTH vs)*tms;
     fs[MULT] expands to tms + LENGTH vs * tms which is decidable *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> rpt strip_tac >>
      gvs[val_in_memory_def, val_wf_def, LET_THM] >>
      conj_tac >> first_x_assum irule >>
      simp[] >> fs[arithmeticTheory.MULT])
  (* 17: kvs cons *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> rpt strip_tac >>
      gvs[val_in_memory_def, LET_THM] >>
      conj_tac
      >- (first_x_assum irule >> simp[])
      >> metis_tac[])
  (* 19: tuple cons *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> rpt strip_tac >>
      Cases_on `tvs` >>
      gvs[val_in_memory_def, val_wf_def, type_memory_size_def, LET_THM,
          AllCaseEqs()] >>
      conj_tac >> first_x_assum irule >> simp[type_memory_size_def])
QED

(* ===== Layer 2: val_in_memory decomposition lemmas ===== *)

(* These are essentially the definition clauses restated as rewrite-friendly
   biconditionals. They simplify consumer proofs by eliminating case splits
   on ty that the definition introduces. *)

(* Struct decomposition: val_in_memory for StructV unfolds to fields_in_memory *)
Theorem val_in_memory_struct_proof:
  ∀ fields field_tvs offset mem.
    val_in_memory (StructTV field_tvs) (StructV fields) offset mem ⇔
    fields_in_memory fields field_tvs offset mem
Proof
  simp[val_in_memory_def]
QED

(* DynArray decomposition *)
Theorem val_in_memory_dynarray_proof:
  ∀ vs elem_tv bound offset mem.
    val_in_memory (ArrayTV elem_tv (Dynamic bound))
                  (ArrayV (DynArrayV vs)) offset mem ⇔
    (mem_word_at offset mem = n2w (LENGTH vs) ∧
     elems_in_memory vs (offset + 32) elem_tv mem)
Proof
  simp[val_in_memory_def]
QED

(* SArray decomposition *)
Theorem val_in_memory_sarray_proof:
  ∀ kvs elem_tv bound offset mem.
    val_in_memory (ArrayTV elem_tv (Fixed bound))
                  (ArrayV (SArrayV kvs)) offset mem ⇔
    kvs_in_memory kvs offset elem_tv mem
Proof
  simp[val_in_memory_def]
QED

(* Tuple decomposition *)
Theorem val_in_memory_tuple_proof:
  ∀ vs tvs offset mem.
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) offset mem ⇔
    tuple_in_memory vs tvs offset mem
Proof
  simp[val_in_memory_def]
QED

(* BytesV with fixed bytes type: word encoding *)
Theorem val_in_memory_fixed_bytes_proof:
  ∀ bs n offset mem.
    val_in_memory (BaseTV (BytesT (Fixed n))) (BytesV bs) offset mem ⇔
    (mem_word_at offset mem =
     typed_val_to_w256 (BaseTV (BytesT (Fixed n))) (BytesV bs))
Proof
  simp[val_in_memory_def]
QED

(* BytesV with AddressT: word encoding *)
Theorem val_in_memory_address_proof:
  ∀ bs offset mem.
    val_in_memory (BaseTV AddressT) (BytesV bs) offset mem ⇔
    (mem_word_at offset mem =
     typed_val_to_w256 (BaseTV AddressT) (BytesV bs))
Proof
  simp[val_in_memory_def]
QED
