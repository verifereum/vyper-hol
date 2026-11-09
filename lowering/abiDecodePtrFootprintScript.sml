Theory abiDecodePtrFootprint
Ancestors
  abiEncoder venomState contractABI words arithmetic
  ptrDiscipline pred_set list abiDecodeStaticProps valueEncodingProps abiStaticAggregateProps abiDecodePtrMemberInterface

Definition abi_decode_runtime_footprint_def:
  abi_decode_runtime_footprint ei p s =
    case ei of
      DecPrimWord w => 32
    | DecBytestring n => 32+contractABI$ceil32 (w2n (mload p s))
    | _ => 0
End

Theorem abi_decode_runtime_footprint_word[simp]:
  abi_decode_runtime_footprint (DecPrimWord w) p s = 32
Proof
  simp[abi_decode_runtime_footprint_def]
QED

Theorem abi_decode_runtime_footprint_bytes[simp]:
  abi_decode_runtime_footprint (DecBytestring n) p s =
    32+contractABI$ceil32 (w2n (mload p s))
Proof
  simp[abi_decode_runtime_footprint_def]
QED

Definition abi_decode_clean_flat_def:
  (abi_decode_clean_flat [] p tn s = T) /\
  (abi_decode_clean_flat ((ei,asz,k)::rest) p tn s <=>
    abi_decode_runtime_footprint ei p s <= k /\
    (!i. p <= i /\ i < p+abi_decode_runtime_footprint ei p s ==>
      i NOTIN tn.t_mem) /\
    abi_decode_clean_flat rest (p+k) tn s)
End

Theorem abi_decode_runtime_footprint_frame:
  abi_decode_runtime_footprint ei p s <= k /\
  (!i. p <= i /\ i < p+k ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) ==>
  abi_decode_runtime_footprint ei p t = abi_decode_runtime_footprint ei p s
Proof
  strip_tac >> Cases_on `ei` >> simp[abi_decode_runtime_footprint_def] >>
  fs[abi_decode_runtime_footprint_def] >>
  `mem_bytes_at p 32 t.vs_memory = mem_bytes_at p 32 s.vs_memory` by
    (irule mem_bytes_at_bytewise >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `mload p t = mload p s` by metis_tac[mem_word_at_bytes, mem_word_at_eq_mload] >>
  simp[]
QED

Theorem abi_decode_runtime_clean_frame:
  abi_decode_runtime_footprint ei p s <= k /\
  (!i. p <= i /\ i < p+abi_decode_runtime_footprint ei p s ==> i NOTIN tn.t_mem) /\
  (!i. p <= i /\ i < p+k ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)) ==>
  abi_decode_runtime_footprint ei p t <= k /\
  (!i. p <= i /\ i < p+abi_decode_runtime_footprint ei p t ==> i NOTIN tf.t_mem)
Proof
  strip_tac >>
  `abi_decode_runtime_footprint ei p t = abi_decode_runtime_footprint ei p s` by
    (irule abi_decode_runtime_footprint_frame >> metis_tac[]) >>
  simp[] >> rpt strip_tac >>
  `p <= i /\ i < p+k` by decide_tac >> metis_tac[]
QED

Theorem abi_decode_runtime_clean_member_frame:
  abi_decode_runtime_footprint ei p s <= k /\
  (!i. p <= i /\ i < p+abi_decode_runtime_footprint ei p s ==> i NOTIN tn.t_mem) /\
  abi_decode_member_frame sa G tn s H tf t a n /\
  (p+k <= a \/ a+n <= p) ==>
  abi_decode_runtime_footprint ei p t <= k /\
  (!i. p <= i /\ i < p+abi_decode_runtime_footprint ei p t ==> i NOTIN tf.t_mem)
Proof
  strip_tac >> irule abi_decode_runtime_clean_frame >>
  qexistsl_tac [`s`, `tn`] >> simp[] >> rpt strip_tac >>
  fs[abi_decode_member_frame_def] >> first_x_assum irule >> decide_tac
QED
