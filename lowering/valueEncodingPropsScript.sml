(*
 * Value Encoding Properties
 *
 * TOP-LEVEL:
 *   val_to_w256_encode_agree — val_to_w256 agrees with vyperStorage encode_base_to_slot
 *   w256_roundtrip           — decode(encode(v)) = v for well-typed primitives
 *   val_in_memory_prim       — primitive val_in_memory reduces to mload check
 *   mem_word_at_eq_mload     — mem_word_at = venomState mload
 *
 * Layer 1 (mstore/mem_word_at):
 *   mstore_mem_word_at_same      — mload after mstore at same offset
 *   mstore_mem_word_at_disjoint  — mload after mstore at disjoint offset
 *   mstore_mem_bytes_at_disjoint — mem_bytes_at after mstore at disjoint offset
 *   mstore_establishes_val_in_memory_prim — mstore with val_to_w256 establishes val_in_memory
 *
 * Layer 2 (compound types):
 *   type_memory_size_prim — primitive base types occupy 32 bytes
 *   type_memory_size_flag — FlagTV occupies 32 bytes
 *   mstore_preserves_val_in_memory — compound disjointness (mutual induction)
 *   val_in_memory_struct  — struct decomposition
 *   val_in_memory_dynarray — dynarray decomposition
 *   val_in_memory_sarray  — sarray decomposition
 *   val_in_memory_tuple   — tuple decomposition
 *   val_in_memory_fixed_bytes — fixed bytes word encoding
 *   val_in_memory_address — address word encoding
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

(* ===== Layer 1: mstore / mem_word_at ===== *)

Theorem mstore_mem_word_at_same:
  ∀ off (w:bytes32) s.
    mem_word_at off (mstore off w s).vs_memory = w
Proof ACCEPT_TAC mstore_mem_word_at_same_proof
QED

Theorem mstore_mem_word_at_disjoint:
  ∀ off1 off2 (w:bytes32) s.
    (off1 + 32 ≤ off2 ∨ off2 + 32 ≤ off1) ⇒
    mem_word_at off1 (mstore off2 w s).vs_memory =
    mem_word_at off1 s.vs_memory
Proof ACCEPT_TAC mstore_mem_word_at_disjoint_proof
QED

Theorem mstore_mem_bytes_at_disjoint:
  ∀ off1 len off2 (w:bytes32) s.
    (off1 + len ≤ off2 ∨ off2 + 32 ≤ off1) ⇒
    mem_bytes_at off1 len (mstore off2 w s).vs_memory =
    mem_bytes_at off1 len s.vs_memory
Proof ACCEPT_TAC mstore_mem_bytes_at_disjoint_proof
QED

Theorem mstore_establishes_val_in_memory_prim:
  ∀ off v s ty.
    (∃ b. v = BoolV b) ∨ (∃ n. v = IntV n) ∨
    (∃ k. v = FlagV k) ∨ (∃ n. v = DecimalV n) ⇒
    val_in_memory ty v off (mstore off (val_to_w256 v) s).vs_memory
Proof ACCEPT_TAC mstore_establishes_val_in_memory_prim_proof
QED

(* ===== Layer 2: type_memory_size ===== *)

Theorem type_memory_size_prim:
  ∀ bt.
    (∀ n. bt ≠ BytesT (Dynamic n)) ∧ (∀ n. bt ≠ StringT n) ⇒
    type_memory_size (BaseTV bt) = 32
Proof ACCEPT_TAC type_memory_size_prim_proof
QED

Theorem type_memory_size_flag:
  ∀ name. type_memory_size (FlagTV name) = 32
Proof ACCEPT_TAC type_memory_size_flag_proof
QED

(* ===== Layer 2: compound disjointness ===== *)

Theorem mstore_preserves_val_in_memory:
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
    (off2 + 32 ≤ off ∨ off + LENGTH vs * type_memory_size tv ≤ off2) ⇒
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
Proof ACCEPT_TAC mstore_preserves_val_in_memory_proof
QED

(* ===== Layer 2: decomposition ===== *)

Theorem val_in_memory_struct:
  ∀ fields field_tvs offset mem.
    val_in_memory (StructTV field_tvs) (StructV fields) offset mem ⇔
    fields_in_memory fields field_tvs offset mem
Proof ACCEPT_TAC val_in_memory_struct_proof
QED

Theorem val_in_memory_dynarray:
  ∀ vs elem_tv bound offset mem.
    val_in_memory (ArrayTV elem_tv (Dynamic bound))
                  (ArrayV (DynArrayV vs)) offset mem ⇔
    (mem_word_at offset mem = n2w (LENGTH vs) ∧
     elems_in_memory vs (offset + 32) elem_tv mem)
Proof ACCEPT_TAC val_in_memory_dynarray_proof
QED

Theorem val_in_memory_sarray:
  ∀ kvs elem_tv bound offset mem.
    val_in_memory (ArrayTV elem_tv (Fixed bound))
                  (ArrayV (SArrayV kvs)) offset mem ⇔
    kvs_in_memory kvs offset elem_tv mem
Proof ACCEPT_TAC val_in_memory_sarray_proof
QED

Theorem val_in_memory_tuple:
  ∀ vs tvs offset mem.
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) offset mem ⇔
    tuple_in_memory vs tvs offset mem
Proof ACCEPT_TAC val_in_memory_tuple_proof
QED

Theorem val_in_memory_fixed_bytes:
  ∀ bs n offset mem.
    val_in_memory (BaseTV (BytesT (Fixed n))) (BytesV bs) offset mem ⇔
    (mem_word_at offset mem =
     typed_val_to_w256 (BaseTV (BytesT (Fixed n))) (BytesV bs))
Proof ACCEPT_TAC val_in_memory_fixed_bytes_proof
QED

Theorem val_in_memory_address:
  ∀ bs offset mem.
    val_in_memory (BaseTV AddressT) (BytesV bs) offset mem ⇔
    (mem_word_at offset mem =
     typed_val_to_w256 (BaseTV AddressT) (BytesV bs))
Proof ACCEPT_TAC val_in_memory_address_proof
QED
