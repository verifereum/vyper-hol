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
  vyperStorage vfmState byte list rich_list combin bitstring
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
