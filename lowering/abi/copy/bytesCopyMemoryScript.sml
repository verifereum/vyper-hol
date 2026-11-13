(* TOP-LEVEL: the runtime-length copy preserves bytes/string values across
   capacity widening and overlapping windows. Helpers give exact memory
   images and preservation outside the written destination range. *)
Theory bytesCopyMemory
Ancestors
  valueEncodingDefs bytesCopyExec bytesSnapshotMemory memoryValueDefs memoryValueFrame
  abiBytestringMemory abiBytestringExec memoryReadProps valueLoadProps
  valueEncoding valueEncodingProps vyperValue vyperTyping vyperAST
  compileEnv contractABI eventTopicValueProps vfmConstants
  venomState venomExecSemantics list words arithmetic

Theorem bytestring_memory_value_raw:
  !tenv ty tv v bs offset mem.
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\ raw_return_bytes v = SOME bs ==>
    (memory_value_rel tv v offset mem <=>
      mem_word_at offset mem = n2w (LENGTH bs) /\
      mem_bytes_at (offset + 32) (LENGTH bs) mem = bs)
Proof
  rpt gen_tac >> strip_tac >> drule bytestring_type_cases >> strip_tac >> gvs[] >>
  drule evaluate_type_base_identity >> DISCH_TAC >> gvs[] >> Cases_on `v` >>
  gvs[raw_return_bytes_def, memory_value_rel_def, val_in_memory_def, LET_THM]
QED

Theorem bytestring_memory_type_irrelevance:
  !tenv fty aty ftv atv v bs offset mem.
    is_bytestring_type fty /\ is_bytestring_type aty /\
    evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv /\
    raw_return_bytes v = SOME bs ==>
    memory_value_rel ftv v offset mem = memory_value_rel atv v offset mem
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`tenv`, `fty`, `ftv`, `v`, `bs`, `offset`, `mem`]
    bytestring_memory_value_raw) >>
  mp_tac (Q.SPECL [`tenv`, `aty`, `atv`, `v`, `bs`, `offset`, `mem`]
    bytestring_memory_value_raw) >> simp[]
QED

Theorem bytes_copy_result_natural_memory:
  !var_base dst_addr src_addr ss payload_len.
    mload (w2n src_addr) ss = n2w payload_len /\
    32 + contractABI$ceil32 payload_len < dimword(:256) ==>
    (bytes_copy_result var_base dst_addr src_addr ss).vs_memory =
      (mcopy (w2n dst_addr) (w2n src_addr) (32 + contractABI$ceil32 payload_len) ss).vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  `payload_len + 31 < dimword(:256)` by
    (mp_tac (Q.SPEC `payload_len` ceil32_bounds) >> decide_tac) >>
  simp[bytes_copy_result_memory, bytestring_round_word_n2w, word_add_n2w, w2n_n2w]
QED

Theorem bytes_copy_result_layout:
  !tenv ty tv v var_base dst_addr src_addr ss.
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
    memory_value_rel tv v (w2n src_addr) ss.vs_memory /\ type_memory_size tv < dimword(:256) ==>
    memory_value_rel tv v (w2n dst_addr)
      (bytes_copy_result var_base dst_addr src_addr ss).vs_memory
Proof
  rpt gen_tac >> strip_tac >> drule_all typed_memory_bytestring_view >> strip_tac >>
  `32 + contractABI$ceil32 (LENGTH bs) < dimword(:256)` by decide_tac >>
  mp_tac (Q.SPECL [`var_base`, `dst_addr`, `src_addr`, `ss`, `LENGTH (bs:byte list)`]
    bytes_copy_result_natural_memory) >> impl_tac >- simp[] >> DISCH_TAC >>
  asm_rewrite_tac [] >>
  mp_tac (Q.SPECL [`tenv`, `ty`, `tv`, `v`, `bs`, `w2n (src_addr:bytes32)`,
    `w2n (dst_addr:bytes32)`, `32 + contractABI$ceil32 (LENGTH (bs:byte list))`, `ss`]
    mcopy_memory_value_bytestring) >> simp[]
QED

Theorem bytes_copy_result_widened_layout:
  !tenv fty aty ftv atv v var_base dst_addr src_addr ss.
    is_bytestring_type fty /\ is_bytestring_type aty /\
    evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv /\
    value_has_type atv v /\ memory_value_rel atv v (w2n src_addr) ss.vs_memory /\
    type_memory_size atv < dimword(:256) ==>
    memory_value_rel ftv v (w2n dst_addr)
      (bytes_copy_result var_base dst_addr src_addr ss).vs_memory
Proof
  rpt gen_tac >> strip_tac >> drule_all typed_memory_bytestring_view >> strip_tac >>
  mp_tac (Q.SPECL [`tenv`, `fty`, `aty`, `ftv`, `atv`, `v`, `bs`, `w2n (dst_addr:bytes32)`,
    `(bytes_copy_result var_base dst_addr src_addr ss).vs_memory`]
    bytestring_memory_type_irrelevance) >> impl_tac >- simp[] >> DISCH_TAC >>
  asm_rewrite_tac [] >>
  mp_tac (Q.SPECL [`tenv`, `aty`, `atv`, `v`, `var_base`, `dst_addr`, `src_addr`, `ss`]
    bytes_copy_result_layout) >> simp[]
QED

Theorem bytes_copy_result_preserves_value:
  !tv v offset var_base dst_addr src_addr ss.
    memory_value_rel tv v offset ss.vs_memory /\ val_wf tv v /\
    (offset + type_memory_size tv <= w2n dst_addr \/
      w2n dst_addr + w2n (bytestring_round_word (mload (w2n src_addr) ss) + 32w) <= offset) ==>
    memory_value_rel tv v offset (bytes_copy_result var_base dst_addr src_addr ss).vs_memory
Proof
  rpt gen_tac >> DISCH_TAC >> PURE_REWRITE_TAC [bytes_copy_result_memory] >>
  irule mcopy_preserves_memory_value_rel >> fs[]
QED

Theorem typed_bytestring_payload_size:
  !tenv ty tv v bs.
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\ raw_return_bytes v = SOME bs ==>
    32 + contractABI$ceil32 (LENGTH bs) <= type_memory_size tv
Proof
  rpt gen_tac >> strip_tac >> drule_all bytestring_value_size_bound >> DISCH_TAC >>
  Cases_on `v` >>
  gvs[raw_return_bytes_def, val_memory_size_def, contractABITheory.ceil32_def, vfmConstantsTheory.word_size_def]
QED

Theorem bytes_copy_result_preserves_field_region:
  !tenv fty aty ftv atv v var_base dst_addr src_addr ss other_tv other_v other_offset.
    is_bytestring_type fty /\ is_bytestring_type aty /\
    evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv /\
    value_has_type ftv v /\ value_has_type atv v /\
    memory_value_rel atv v (w2n src_addr) ss.vs_memory /\ type_memory_size atv < dimword(:256) /\
    memory_value_rel other_tv other_v other_offset ss.vs_memory /\ val_wf other_tv other_v /\
    (other_offset + type_memory_size other_tv <= w2n dst_addr \/
      w2n dst_addr + type_memory_size ftv <= other_offset) ==>
    memory_value_rel other_tv other_v other_offset
      (bytes_copy_result var_base dst_addr src_addr ss).vs_memory
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all typed_memory_bytestring_view >> strip_tac >>
  `32 + contractABI$ceil32 (LENGTH bs) < dimword(:256)` by decide_tac >>
  `32 + contractABI$ceil32 (LENGTH bs) <= type_memory_size ftv` by
    (mp_tac (Q.SPECL [`tenv`, `fty`, `ftv`, `v`, `bs`] typed_bytestring_payload_size) >> simp[]) >>
  mp_tac (Q.SPECL [`var_base`, `dst_addr`, `src_addr`, `ss`, `LENGTH (bs:byte list)`]
    bytes_copy_result_natural_memory) >> impl_tac >- simp[] >> DISCH_TAC >>
  asm_rewrite_tac [] >>
  mp_tac (Q.SPECL [`other_tv`, `other_v`, `other_offset`, `w2n (dst_addr:bytes32)`,
    `w2n (src_addr:bytes32)`, `32 + contractABI$ceil32 (LENGTH (bs:byte list))`, `ss`]
    mcopy_preserves_memory_value_rel) >>
  impl_tac >- (conj_tac >- simp[] >> conj_tac >- simp[] >> decide_tac) >> simp[]
QED
