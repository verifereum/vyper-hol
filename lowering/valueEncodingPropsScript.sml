(*
 * Value Encoding Properties
 *
 * TOP-LEVEL:
 *   val_to_w256_encode_agree — val_to_w256 agrees with vyperStorage encode_base_to_slot
 *   w256_roundtrip           — decode(encode(v)) = v for well-typed primitives
 *   val_in_memory_mload      — primitive val_in_memory reduces to mload check
 *   mem_word_at_mload        — mem_word_at = venomState mload
 *)

Theory valueEncodingProps
Ancestors
  valueEncoding valueEncodingProofs

(* ===== val_to_w256 agrees with encode_base_to_slot ===== *)

Theorem val_to_w256_encode_agree:
  ∀ v tv w.
    encode_base_to_slot v tv = SOME w ∧
    (∀ bs n. v = BytesV bs ∧ tv = BaseTV (BytesT (Fixed n)) ⇒ F)
    ⇒
    val_to_w256 v = w
Proof
  ACCEPT_TAC val_to_w256_encode_agree_proof
QED

(* ===== Roundtrip: decode ∘ encode = id ===== *)

Theorem w256_roundtrip:
  ∀ v tv w.
    encode_base_to_slot v tv = SOME w ∧
    (∀ i n. v = IntV i ∧ tv = BaseTV (UintT n) ⇒
            0 ≤ i ∧ i < &(dimword (:256))) ∧
    (∀ i n. v = IntV i ∧ tv = BaseTV (IntT n) ⇒
            INT_MIN (:256) ≤ i ∧ i ≤ INT_MAX (:256)) ∧
    (∀ k. v = FlagV k ⇒ k < dimword (:256)) ∧
    (∀ n. v = DecimalV n ⇒ INT_MIN (:256) ≤ n ∧ n ≤ INT_MAX (:256))
    ⇒
    w256_to_val w tv = v
Proof
  ACCEPT_TAC w256_roundtrip_proof
QED

(* ===== mem_word_at agrees with venomState mload ===== *)

Theorem mem_word_at_eq_mload:
  ∀ offset s.
    mem_word_at offset s.vs_memory = mload offset s
Proof
  ACCEPT_TAC mem_word_at_eq_mload_proof
QED

(* ===== Primitive val_in_memory reduces to word check ===== *)

Theorem val_in_memory_prim:
  ∀ v offset mem ty.
    (∃ b. v = BoolV b) ∨ (∃ n. v = IntV n) ∨
    (∃ k. v = FlagV k) ∨ (∃ n. v = DecimalV n) ⇒
    (val_in_memory ty v offset mem ⇔
      mem_word_at offset mem = val_to_w256 v)
Proof
  ACCEPT_TAC val_in_memory_prim_proof
QED
