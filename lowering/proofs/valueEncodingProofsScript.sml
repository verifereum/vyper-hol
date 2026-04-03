(*
 * Value Encoding Proofs
 *
 * Proves theorems exported by valueEncodingPropsScript.
 *)

Theory valueEncodingProofs
Ancestors
  valueEncoding vyperStorage venomState
Libs
  blastLib

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

Theorem w256_roundtrip_proof:
  ∀ v tv w.
    encode_base_to_slot v tv = SOME w ∧
    (* Well-typedness: value fits in word (conditioned on type) *)
    (∀ i n. v = IntV i ∧ tv = BaseTV (UintT n) ⇒
            0 ≤ i ∧ i < &(dimword (:256))) ∧
    (∀ i n. v = IntV i ∧ tv = BaseTV (IntT n) ⇒
            INT_MIN (:256) ≤ i ∧ i ≤ INT_MAX (:256)) ∧
    (∀ k. v = FlagV k ⇒ k < dimword (:256)) ∧
    (∀ n. v = DecimalV n ⇒ INT_MIN (:256) ≤ n ∧ n ≤ INT_MAX (:256))
    ⇒
    w256_to_val w tv = v
Proof
  Cases_on `v` >> Cases_on `tv` >>
  simp[encode_base_to_slot_def, w256_to_val_def,
       decode_base_from_slot_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  rename1 `encode_base_to_slot _ (BaseTV bt) = SOME _` >>
  Cases_on `bt` >>
  gvs[encode_base_to_slot_def, decode_base_from_slot_def,
      bool_to_slot_def, slot_to_bool_def, AllCaseEqs(),
      integer_wordTheory.w2n_i2w, integer_wordTheory.w2i_i2w,
      integerTheory.INT_LESS_MOD] >>
  TRY (Cases_on `b` >> gvs[bool_to_slot_def, slot_to_bool_def] >> NO_TAC) >>
  (* BytesV + BytesT: split bound; BytesV + AddressT: pad_left roundtrip *)
  FIRST [
    Cases_on `b` >>
    gvs[encode_base_to_slot_def, decode_base_from_slot_def,
        AllCaseEqs(), TAKE_word_to_bytes_be_word_of_bytes_be],
    simp[word_to_bytes_be_pad_left_roundtrip]
  ]
QED

(* ===== mem_word_at = mload ===== *)

Theorem mem_word_at_eq_mload_proof:
  ∀ offset s.
    mem_word_at offset s.vs_memory = mload offset s
Proof
  rw[mem_word_at_def, mload_def]
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
   Works at the venom_state level. *)
Theorem mstore_mem_word_at_same_proof:
  ∀ off (w:bytes32) s.
    mem_word_at off (mstore off w s).vs_memory = w
Proof
  cheat
QED

(* mstore at off2 preserves mem_word_at at off1 when regions don't overlap.
   Regions are [off1, off1+32) and [off2, off2+32). *)
Theorem mstore_mem_word_at_disjoint_proof:
  ∀ off1 off2 (w:bytes32) s.
    (off1 + 32 ≤ off2 ∨ off2 + 32 ≤ off1) ⇒
    mem_word_at off1 (mstore off2 w s).vs_memory =
    mem_word_at off1 s.vs_memory
Proof
  cheat
QED

(* mstore at off2 preserves mem_bytes_at at off1 when regions don't overlap.
   Regions are [off1, off1+len) and [off2, off2+32). *)
Theorem mstore_mem_bytes_at_disjoint_proof:
  ∀ off1 len off2 (w:bytes32) s.
    (off1 + len ≤ off2 ∨ off2 + 32 ≤ off1) ⇒
    mem_bytes_at off1 len (mstore off2 w s).vs_memory =
    mem_bytes_at off1 len s.vs_memory
Proof
  cheat
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
  cheat
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

   This is the key theorem for compound types. It requires mutual
   induction on val_in_memory's recursive structure (val, fields,
   elems, kvs, tuple). *)
Theorem mstore_preserves_val_in_memory_proof:
  (∀ ty v off mem off2 (w:bytes32).
    val_in_memory ty v off mem ∧
    (off2 + 32 ≤ off ∨ off + type_memory_size ty ≤ off2) ⇒
    val_in_memory ty v off (mstore off2 w (s with vs_memory := mem)).vs_memory) ∧
  (∀ fields field_tvs off mem off2 (w:bytes32).
    fields_in_memory fields field_tvs off mem ∧
    (off2 + 32 ≤ off ∨ off + type_memory_size_fields field_tvs ≤ off2) ⇒
    fields_in_memory fields field_tvs off
      (mstore off2 w (s with vs_memory := mem)).vs_memory) ∧
  (∀ vs off tv mem off2 (w:bytes32).
    elems_in_memory vs off tv mem ∧
    (off2 + 32 ≤ off ∨
     off + LENGTH vs * type_memory_size tv ≤ off2) ⇒
    elems_in_memory vs off tv
      (mstore off2 w (s with vs_memory := mem)).vs_memory) ∧
  (∀ (kvs : (num # value) list) base_off tv mem off2 (w:bytes32).
    kvs_in_memory kvs base_off tv mem ∧
    (∀ k v. MEM (k,v) kvs ⇒
      off2 + 32 ≤ base_off + k * type_memory_size tv ∨
      base_off + k * type_memory_size tv + type_memory_size tv ≤ off2) ⇒
    kvs_in_memory kvs base_off tv
      (mstore off2 w (s with vs_memory := mem)).vs_memory) ∧
  (∀ vs tvs off mem off2 (w:bytes32).
    tuple_in_memory vs tvs off mem ∧
    (off2 + 32 ≤ off ∨ off + type_memory_size_list tvs ≤ off2) ⇒
    tuple_in_memory vs tvs off
      (mstore off2 w (s with vs_memory := mem)).vs_memory)
Proof
  cheat
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
