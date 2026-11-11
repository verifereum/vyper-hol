Theory loadElimMemoryRel
Ancestors
  venomState stateFrame pred_set list rich_list codegenRel regularCallEmitSim venomMemProps loadElimByteHelpers

Definition padded_exec_equiv_def:
  padded_exec_equiv vars s1 s2 <=>
    (!v. v NOTIN vars ==> lookup_var v s1 = lookup_var v s2) /\
    (!i. venomState$read_memory i 1 s1 = venomState$read_memory i 1 s2) /\
    execution_frame (s1 with vs_memory := []) =
    execution_frame (s2 with vs_memory := [])
End

Theorem padded_exec_equiv_refl:
  !vars s. padded_exec_equiv vars s s
Proof
  simp[padded_exec_equiv_def]
QED

Theorem padded_exec_equiv_trans:
  !vars s1 s2 s3.
    padded_exec_equiv vars s1 s2 /\ padded_exec_equiv vars s2 s3 ==>
    padded_exec_equiv vars s1 s3
Proof
  rw[padded_exec_equiv_def] >> metis_tac[]
QED

Theorem padded_exec_equiv_sym:
  !vars s1 s2. padded_exec_equiv vars s1 s2 ==>
    padded_exec_equiv vars s2 s1
Proof
  rw[padded_exec_equiv_def] >> metis_tac[]
QED

Theorem read_memory_length:
  !n i s. LENGTH (venomState$read_memory i n s) = n
Proof
  simp[venomStateTheory.read_memory_def, LENGTH_TAKE_EQ]
QED

Theorem read_memory_byte:
  !n i s j. j < n ==>
    EL j (venomState$read_memory i n s) =
    if i + j < LENGTH s.vs_memory then EL (i + j) s.vs_memory else 0w
Proof
  rpt strip_tac >> simp[venomStateTheory.read_memory_def, EL_TAKE, EL_APPEND_EQN,
    LENGTH_DROP, EL_DROP, EL_REPLICATE] >>
  Cases_on `i + j < LENGTH s.vs_memory` >> gvs[]
QED

Theorem read_memory_range_ext:
  !s1 s2. (!i. venomState$read_memory i 1 s1 = venomState$read_memory i 1 s2) ==>
    !i n. venomState$read_memory i n s1 = venomState$read_memory i n s2
Proof
  rpt strip_tac >> irule listTheory.LIST_EQ >> simp[read_memory_length] >>
  qx_gen_tac `j` >> strip_tac >>
  first_x_assum (qspec_then `i + j` mp_tac) >>
  disch_then (mp_tac o Q.AP_TERM `EL 0`) >>
  simp[read_memory_byte]
QED

Theorem padded_exec_equiv_mload:
  !vars s1 s2 i. padded_exec_equiv vars s1 s2 ==>
    mload i s1 = mload i s2
Proof
  rpt strip_tac >>
  `venomState$read_memory i 32 s1 = venomState$read_memory i 32 s2` by
    (irule read_memory_range_ext >> gvs[padded_exec_equiv_def]) >>
  gvs[mload_def, venomStateTheory.read_memory_def]
QED


(* Reuse codegenRel's total read_byte observer rather than introducing an
   identical padded_byte. Its expanded-write law is already exported by
   regularCallEmitSimTheory.read_byte_write_memory_with_expansion. *)
Theorem read_byte_zero_append:
  read_byte j (m ++ REPLICATE n 0w) = read_byte j m
Proof
  simp[read_byte_def, EL_APPEND_EQN, EL_REPLICATE] >>
  Cases_on `j < LENGTH m` >> simp[]
QED

Theorem read_memory_read_byte:
  j < n ==> EL j (venomState$read_memory i n s) = read_byte (i + j) s.vs_memory
Proof
  simp[read_memory_byte, read_byte_def]
QED

Theorem read_memory_read_byte_ext:
  (!j. read_byte j s1.vs_memory = read_byte j s2.vs_memory) ==>
  venomState$read_memory i n s1 = venomState$read_memory i n s2
Proof
  strip_tac >> irule listTheory.LIST_EQ >> simp[read_memory_length] >>
  simp[read_memory_read_byte]
QED

Theorem read_memory_write_read_slice:
  venomState$read_memory i k
    (write_memory_with_expansion off (venomState$read_memory off n s) s) =
  venomState$read_memory i k s
Proof
  irule read_memory_read_byte_ext >> gen_tac >>
  simp[read_byte_write_memory_with_expansion, read_memory_length] >>
  IF_CASES_TAC >-
    (`j - off < n` by decide_tac >>
     simp[read_memory_read_byte]) >>
  simp[]
QED

Theorem mstore_mload_write_slice:
  mstore off (mload off s) s =
    write_memory_with_expansion off (venomState$read_memory off 32 s) s
Proof
  `word_to_bytes (mload off s) T = venomState$read_memory off 32 s` by
    (rewrite_tac[venomStateTheory.mload_def, GSYM venomStateTheory.read_memory_def] >>
     simp[LET_THM] >> irule word_bytes_roundtrip_256 >> simp[read_memory_length]) >>
  simp[mstore_def, write_memory_with_expansion_def, read_memory_length,
    byteTheory.LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem padded_exec_equiv_mstore_mload:
  padded_exec_equiv vars s (mstore off (mload off s) s)
Proof
  rewrite_tac[padded_exec_equiv_def] >> conj_tac
  >- simp[lookup_var_def, mstore_def] >>
  conj_tac
  >- (gen_tac >> sym_tac >> rewrite_tac[mstore_mload_write_slice] >>
      irule read_memory_write_read_slice) >>
  simp[mstore_def, stateFrameTheory.execution_frame_def]
QED

Theorem padded_exec_equiv_empty_zero_store:
  padded_exec_equiv {} (s with vs_memory := [])
    (mstore 0 0w (s with vs_memory := []))
Proof
  `mload 0 (s with vs_memory := []) = 0w` by
    simp[venomStateTheory.mload_def, listTheory.TAKE_LENGTH_ID_rwt, word_of_bytes_zero_256] >>
  metis_tac[padded_exec_equiv_mstore_mload]
QED
