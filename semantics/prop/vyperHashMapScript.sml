(*
 * vyperHashMapScript.sml
 *
 * Properties of Vyper HashMap values backed by storage slots.
 * Analogous to vyperArrayScript.sml but for storage-backed HashMaps.
 *
 * TOP-LEVEL:
 *   hashmap_slot_for_def    - compute storage slot for a key
 *   hashmap_read_def        - read value at a HashMap key
 *   hashmap_write_def       - write value at a HashMap key
 *   hashmap_slots_disjoint_def - two keys have non-overlapping slot ranges
 *   no_hashmap_collision_def   - all distinct encoded keys have disjoint slots
 *
 *   hashmap_write_some             - write succeeds for well-typed values
 *   hashmap_read_after_write_same  - read at same key returns written value
 *   hashmap_read_after_write_other - read at different key is unchanged
 *)

Theory vyperHashMap
Ancestors
  vyperEncodeDecode vyperTyping vyperState
Libs
  wordsLib

(* ===== Shorthand Definitions ===== *)

(* Compute the storage slot for a HashMap entry *)
Definition hashmap_slot_for_def:
  hashmap_slot_for base kt kv =
    hashmap_slot base (encode_hashmap_key kt kv)
End

(* Read a value from a HashMap entry in storage *)
Definition hashmap_read_def:
  hashmap_read storage base kt tv kv =
    decode_value storage (w2n (hashmap_slot_for base kt kv)) tv
End

(* Write a value to a HashMap entry in storage, returning updated storage *)
Definition hashmap_write_def:
  hashmap_write storage base kt tv kv v =
    case encode_value tv v of
    | SOME writes =>
        SOME (apply_writes (hashmap_slot_for base kt kv) writes storage)
    | NONE => NONE
End

(* ===== Collision-Freedom Definitions ===== *)

(* Two HashMap keys have non-overlapping storage slot ranges.
   A value of type tv occupies type_slot_size tv consecutive slots starting
   at the computed slot. Two keys are disjoint when their ranges don't overlap
   and both fit within the 256-bit address space. *)
Definition hashmap_slots_disjoint_def:
  hashmap_slots_disjoint base kt tv kv1 kv2 ⇔
    let s1 = w2n (hashmap_slot_for base kt kv1) in
    let s2 = w2n (hashmap_slot_for base kt kv2) in
      s1 + type_slot_size tv ≤ dimword(:256) ∧
      s2 + type_slot_size tv ≤ dimword(:256) ∧
      (s1 + type_slot_size tv ≤ s2 ∨ s2 + type_slot_size tv ≤ s1)
End

(* Global no-collision property: all pairs of keys with distinct encodings
   have disjoint slot ranges. This is an assumption about Keccak-256
   collision resistance combined with slot range non-overlap. *)
Definition no_hashmap_collision_def:
  no_hashmap_collision base kt tv ⇔
    ∀kv1 kv2. encode_hashmap_key kt kv1 ≠ encode_hashmap_key kt kv2 ⇒
      hashmap_slots_disjoint base kt tv kv1 kv2
End

(* ===== Basic Properties ===== *)

Theorem hashmap_slots_disjoint_sym:
  ∀base kt tv kv1 kv2.
    hashmap_slots_disjoint base kt tv kv1 kv2 ⇔
    hashmap_slots_disjoint base kt tv kv2 kv1
Proof
  rw[hashmap_slots_disjoint_def, LET_THM]
  \\ metis_tac[]
QED

Theorem no_hashmap_collision_imp:
  ∀base kt tv kv1 kv2.
    no_hashmap_collision base kt tv ∧
    encode_hashmap_key kt kv1 ≠ encode_hashmap_key kt kv2 ⇒
    hashmap_slots_disjoint base kt tv kv1 kv2
Proof
  rw[no_hashmap_collision_def]
QED

Theorem hashmap_slot_for_eq:
  ∀base kt kv1 kv2.
    encode_hashmap_key kt kv1 = encode_hashmap_key kt kv2 ⇒
    hashmap_slot_for base kt kv1 = hashmap_slot_for base kt kv2
Proof
  rw[hashmap_slot_for_def]
QED

Theorem hashmap_read_eq_slot:
  ∀storage base kt tv kv.
    hashmap_read storage base kt tv kv =
    decode_value storage (w2n (hashmap_slot_for base kt kv)) tv
Proof
  rw[hashmap_read_def]
QED

(* ===== Write Success ===== *)

Theorem hashmap_write_some:
  ∀storage base kt tv kv v.
    value_has_type tv v ⇒
    ∃storage'. hashmap_write storage base kt tv kv v = SOME storage'
Proof
  rw[hashmap_write_def]
  \\ `IS_SOME (encode_value tv v)` by
    metis_tac[CONJUNCT1 value_has_type_equiv]
  \\ Cases_on `encode_value tv v` \\ gvs[]
QED

(* ===== Read After Write: Same Key ===== *)

Theorem hashmap_read_after_write_same:
  ∀storage base kt tv kv v.
    value_has_type tv v ∧ well_formed_type_value tv ⇒
    ∃storage'.
      hashmap_write storage base kt tv kv v = SOME storage' ∧
      hashmap_read storage' base kt tv kv = SOME v
Proof
  rw[hashmap_write_def, hashmap_read_def]
  \\ `IS_SOME (encode_value tv v)` by
    metis_tac[CONJUNCT1 value_has_type_equiv]
  \\ Cases_on `encode_value tv v` \\ gvs[]
  \\ `encode_decode_roundtrip_ok tv v` by
    metis_tac[encode_decode_roundtrip_all]
  \\ fs[encode_decode_roundtrip_ok_def]
  \\ metis_tac[wordsTheory.n2w_w2n]
QED

(* ===== Read After Write: Different Key ===== *)

Theorem decode_value_disjoint_writes_word[local]:
  ∀tv writes (slot1:bytes32) (slot2:bytes32) storage sz.
    (∀wr_off. MEM wr_off (MAP FST writes) ⇒ wr_off < sz) ∧
    w2n slot1 + sz ≤ dimword(:256) ∧
    w2n slot2 + type_slot_size tv ≤ dimword(:256) ∧
    (w2n slot1 + sz ≤ w2n slot2 ∨ w2n slot2 + type_slot_size tv ≤ w2n slot1) ⇒
    decode_value (apply_writes slot1 writes storage) (w2n slot2) tv =
    decode_value storage (w2n slot2) tv
Proof
  rpt gen_tac \\ strip_tac
  \\ `decode_value (apply_writes (n2w (w2n slot1)) writes storage)
        (w2n slot2) tv =
      decode_value storage (w2n slot2) tv` suffices_by simp[wordsTheory.n2w_w2n]
  \\ irule decode_value_disjoint_writes
  \\ simp[] \\ qexists_tac `sz` \\ fs[]
QED

Theorem hashmap_read_after_write_other:
  ∀storage storage' base kt tv kv1 kv2 v.
    hashmap_write storage base kt tv kv1 v = SOME storage' ∧
    value_has_type tv v ∧
    hashmap_slots_disjoint base kt tv kv1 kv2 ⇒
    hashmap_read storage' base kt tv kv2 =
    hashmap_read storage base kt tv kv2
Proof
  rw[hashmap_write_def, hashmap_read_def, AllCaseEqs(),
     hashmap_slots_disjoint_def, LET_THM]
  \\ irule decode_value_disjoint_writes_word
  \\ simp[]
  \\ qexists_tac `type_slot_size tv`
  \\ simp[]
  \\ drule (CONJUNCT1 encode_writes_bounded) \\ simp[]
QED

(* Variant using no_hashmap_collision *)
Theorem hashmap_read_after_write_other_no_collision:
  ∀storage storage' base kt tv kv1 kv2 v.
    hashmap_write storage base kt tv kv1 v = SOME storage' ∧
    value_has_type tv v ∧
    no_hashmap_collision base kt tv ∧
    encode_hashmap_key kt kv1 ≠ encode_hashmap_key kt kv2 ⇒
    hashmap_read storage' base kt tv kv2 =
    hashmap_read storage base kt tv kv2
Proof
  rpt strip_tac
  \\ irule hashmap_read_after_write_other
  \\ metis_tac[no_hashmap_collision_imp]
QED

(* ===== compute_hashmap_slot Properties ===== *)

Theorem compute_hashmap_slot_nil:
  ∀slot. compute_hashmap_slot slot [] [] = SOME slot
Proof
  simp[compute_hashmap_slot_def]
QED

Theorem compute_hashmap_slot_single:
  ∀slot kt k.
    subscript_to_value k = SOME kv ⇒
    compute_hashmap_slot slot [kt] [k] =
    SOME (hashmap_slot slot (encode_hashmap_key kt kv))
Proof
  rw[compute_hashmap_slot_def]
QED

Theorem compute_hashmap_slot_cons:
  ∀slot kt kts k ks kv.
    subscript_to_value k = SOME kv ⇒
    compute_hashmap_slot slot (kt::kts) (k::ks) =
    compute_hashmap_slot (hashmap_slot slot (encode_hashmap_key kt kv)) kts ks
Proof
  rw[compute_hashmap_slot_def]
QED

Theorem compute_hashmap_slot_length_mismatch:
  ∀slot kt kts.
    LENGTH kts ≠ 0 ⇒
    compute_hashmap_slot slot (kt::kts) [] = NONE
Proof
  simp[compute_hashmap_slot_def]
QED

Theorem compute_hashmap_slot_none_bad_subscript:
  ∀slot kt kts k ks.
    subscript_to_value k = NONE ⇒
    compute_hashmap_slot slot (kt::kts) (k::ks) = NONE
Proof
  rw[compute_hashmap_slot_def]
QED

Theorem compute_hashmap_slot_some_length:
  ∀slot kts ks result.
    compute_hashmap_slot slot kts ks = SOME result ⇒
    LENGTH kts = LENGTH ks
Proof
  ho_match_mp_tac compute_hashmap_slot_ind
  \\ rw[compute_hashmap_slot_def]
  \\ gvs[AllCaseEqs()]
QED

Theorem compute_hashmap_slot_append:
  ∀slot kts1 ks1 kts2 ks2 mid_slot.
    compute_hashmap_slot slot kts1 ks1 = SOME mid_slot ⇒
    compute_hashmap_slot slot (kts1 ++ kts2) (ks1 ++ ks2) =
    compute_hashmap_slot mid_slot kts2 ks2
Proof
  ho_match_mp_tac compute_hashmap_slot_ind
  \\ rw[compute_hashmap_slot_def]
  \\ gvs[AllCaseEqs()]
QED

(* ===== hashmap_slot properties ===== *)

(* hashmap_slot is deterministic in its arguments *)
Theorem hashmap_slot_cong:
  ∀base k1 k2. k1 = k2 ⇒ hashmap_slot base k1 = hashmap_slot base k2
Proof
  simp[]
QED

(* hashmap_slot unfolds to keccak256 of concatenated bytes *)
Theorem hashmap_slot_unfold:
  ∀base k.
    hashmap_slot base k =
    word_of_bytes_be (Keccak_256_w64 (word_to_bytes_be base ++ word_to_bytes_be k))
Proof
  simp[vyperStorageTheory.hashmap_slot_def]
QED

(* ===== evaluate_subscript for HashMaps ===== *)

Theorem evaluate_subscript_hashmap_nested:
  ∀tenv tv base is_transient slot kt kt' vt' kv.
    evaluate_subscript tenv tv
      (HashMapRef is_transient slot kt (HashMapT kt' vt')) kv =
    INL (INL (HashMapRef is_transient
      (hashmap_slot slot (encode_hashmap_key kt kv)) kt' vt'))
Proof
  rw[evaluate_subscript_def]
QED

Theorem evaluate_subscript_hashmap_leaf:
  ∀tenv tv base is_transient slot kt t kv result_tv.
    evaluate_type tenv t = SOME result_tv ⇒
    evaluate_subscript tenv tv
      (HashMapRef is_transient slot kt (Type t)) kv =
    INL (INR (is_transient,
              hashmap_slot slot (encode_hashmap_key kt kv),
              result_tv))
Proof
  rw[evaluate_subscript_def]
QED

(* ===== encode_hashmap_key Properties ===== *)

Theorem encode_hashmap_key_int[simp]:
  ∀i kt. encode_hashmap_key kt (IntV i) = (i2w i : bytes32)
Proof
  simp[vyperStorageTheory.encode_hashmap_key_def]
QED

Theorem encode_hashmap_key_flag[simp]:
  ∀n kt. encode_hashmap_key kt (FlagV n) = (n2w n : bytes32)
Proof
  simp[vyperStorageTheory.encode_hashmap_key_def]
QED

Theorem encode_hashmap_key_bool[simp]:
  ∀b kt. encode_hashmap_key kt (BoolV b) = if b then 1w else (0w : bytes32)
Proof
  simp[vyperStorageTheory.encode_hashmap_key_def]
QED

(* ===== split_hashmap_subscripts properties ===== *)

Theorem split_hashmap_subscripts_type:
  ∀t subs. split_hashmap_subscripts (Type t) subs = SOME (t, [], subs)
Proof
  simp[split_hashmap_subscripts_def]
QED

Theorem split_hashmap_subscripts_hashmap_nil:
  ∀kt vt. split_hashmap_subscripts (HashMapT kt vt) [] = NONE
Proof
  simp[split_hashmap_subscripts_def]
QED

Theorem split_hashmap_subscripts_some_key_types_length:
  ∀vt subs t kts remaining.
    split_hashmap_subscripts vt subs = SOME (t, kts, remaining) ⇒
    LENGTH kts + LENGTH remaining + 1 ≤ LENGTH subs + 1
Proof
  ho_match_mp_tac split_hashmap_subscripts_ind
  \\ rw[split_hashmap_subscripts_def]
  \\ gvs[AllCaseEqs()]
QED
