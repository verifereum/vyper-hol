(* TOP-LEVEL: copying the rounded live bytes preserves a typed bytes/string
   value, including empty values and overlapping memory windows. No facts
   about unused capacity or padding bytes are required. *)
Theory bytesSnapshotMemory
Ancestors
  valueEncodingDefs bytesSnapshotExec memoryValueRelocation memoryValueDefs memoryValueFrame
  valueLoadProps eventTopicValueProps abiBytestringMemory abiBytestringExec
  memoryReadProps valueEncoding valueEncodingProps compileEnv
  vyperValue vyperTyping vyperAST contractABI vfmConstants
  venomState venomExecSemantics list words arithmetic

Theorem bytestring_type_cases:
  !ty. is_bytestring_type ty ==>
    (?cap. ty = BaseT (StringT cap)) \/ (?cap. ty = BaseT (BytesT (Dynamic cap)))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ty` >> gvs[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >> gvs[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT (BytesT byte_bound))` >>
  Cases_on `byte_bound` >> gvs[is_bytestring_type_def]
QED

Theorem typed_memory_bytestring_view:
  !tenv ty tv v offset (ss:venom_state).
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
    memory_value_rel tv v offset ss.vs_memory ==>
    ?bs. raw_return_bytes v = SOME bs /\ mload offset ss = n2w (LENGTH bs) /\
      read_memory (offset + 32) (LENGTH bs) ss = bs /\
      32 + contractABI$ceil32 (LENGTH bs) <= type_memory_size tv
Proof
  rpt gen_tac >> strip_tac >>
  `val_memory_size v <= type_memory_size tv` by
    (drule_all bytestring_value_size_bound >> simp[]) >>
  drule bytestring_type_cases >> strip_tac >> gvs[] >>
  drule evaluate_type_base_identity >> DISCH_TAC >> gvs[] >> Cases_on `v` >>
  gvs[value_has_type_def, raw_return_bytes_def, memory_value_rel_def, val_in_memory_def,
    val_memory_size_def, type_memory_size_def, read_memory_eq_mem_bytes_at,
    mem_word_at_eq_mload, contractABITheory.ceil32_def, vfmConstantsTheory.word_size_def, LET_THM]
QED

Theorem mcopy_live_bytestring_reads:
  !dst src copied_count payload_len (ss:venom_state).
    32 + payload_len <= copied_count ==>
    mload dst (mcopy dst src copied_count ss) = mload src ss /\
    read_memory (dst + 32) payload_len (mcopy dst src copied_count ss) =
      read_memory (src + 32) payload_len ss
Proof
  rpt gen_tac >> DISCH_TAC >> conj_tac
  >- (PURE_REWRITE_TAC [mload_read_memory] >> AP_TERM_TAC >>
      irule read_memory_mcopy_prefix >> decide_tac) >>
  mp_tac (Q.SPECL [`dst`, `copied_count`, `32`, `payload_len`,
    `mcopy dst src copied_count ss`] read_memory_subwindow) >>
  mp_tac (Q.SPECL [`src`, `copied_count`, `32`, `payload_len`, `ss`] read_memory_subwindow) >>
  simp[read_memory_mcopy_self]
QED

Theorem mcopy_memory_value_bytestring:
  !tenv ty tv v bs src dst copied_count (ss:venom_state).
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\ raw_return_bytes v = SOME bs /\
    memory_value_rel tv v src ss.vs_memory /\ 32 + LENGTH bs <= copied_count ==>
    memory_value_rel tv v dst (mcopy dst src copied_count ss).vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`dst`, `src`, `copied_count`, `LENGTH (bs:byte list)`, `ss`]
    mcopy_live_bytestring_reads) >> impl_tac >- simp[] >> DISCH_TAC >>
  drule bytestring_type_cases >> strip_tac >> gvs[] >>
  drule evaluate_type_base_identity >> DISCH_TAC >> gvs[] >> Cases_on `v` >>
  gvs[raw_return_bytes_def, memory_value_rel_def, val_in_memory_def, LET_THM,
    mem_word_at_eq_mload, GSYM read_memory_eq_mem_bytes_at]
QED

Theorem bytes_snapshot_result_natural_memory:
  !id var_base capacity src_addr ss payload_len.
    mload (w2n src_addr) ss = n2w payload_len /\
    32 + contractABI$ceil32 payload_len < dimword(:256) ==>
    (bytes_snapshot_result id var_base capacity src_addr ss).vs_memory =
      (mcopy (w2n (memory_snapshot_addr id ss)) (w2n src_addr)
        (32 + contractABI$ceil32 payload_len) ss).vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  `payload_len + 31 < dimword(:256)` by
    (mp_tac (Q.SPEC `payload_len` ceil32_bounds) >> decide_tac) >>
  simp[bytes_snapshot_result_memory, bytestring_round_word_n2w, word_add_n2w, w2n_n2w]
QED

Theorem bytes_snapshot_result_layout:
  !tenv ty tv v id var_base capacity src_addr ss.
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
    memory_value_rel tv v (w2n src_addr) ss.vs_memory /\ type_memory_size tv < dimword(:256) ==>
    memory_value_rel tv v (w2n (memory_snapshot_addr id ss))
      (bytes_snapshot_result id var_base capacity src_addr ss).vs_memory
Proof
  rpt gen_tac >> strip_tac >> drule_all typed_memory_bytestring_view >> strip_tac >>
  `32 + contractABI$ceil32 (LENGTH bs) < dimword(:256)` by decide_tac >>
  mp_tac (Q.SPECL [`id`, `var_base`, `capacity`, `src_addr`, `ss`, `LENGTH (bs:byte list)`]
    bytes_snapshot_result_natural_memory) >> impl_tac >- simp[] >> DISCH_TAC >>
  asm_rewrite_tac [] >>
  mp_tac (Q.SPECL [`tenv`, `ty`, `tv`, `v`, `bs`, `w2n (src_addr:bytes32)`,
    `w2n (memory_snapshot_addr id ss)`, `32 + contractABI$ceil32 (LENGTH (bs:byte list))`, `ss`]
    mcopy_memory_value_bytestring) >> simp[]
QED

Theorem bytes_snapshot_result_preserves_value:
  !tenv ty tv v id var_base capacity src_addr ss other_tv other_v other_offset.
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
    memory_value_rel tv v (w2n src_addr) ss.vs_memory /\
    type_memory_size tv <= capacity /\ type_memory_size tv < dimword(:256) /\
    memory_value_rel other_tv other_v other_offset ss.vs_memory /\ val_wf other_tv other_v /\
    (other_offset + type_memory_size other_tv <= w2n (memory_snapshot_addr id ss) \/
      w2n (memory_snapshot_addr id ss) + capacity <= other_offset) ==>
    memory_value_rel other_tv other_v other_offset
      (bytes_snapshot_result id var_base capacity src_addr ss).vs_memory
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all typed_memory_bytestring_view >> strip_tac >>
  `32 + contractABI$ceil32 (LENGTH bs) < dimword(:256)` by decide_tac >>
  mp_tac (Q.SPECL [`id`, `var_base`, `capacity`, `src_addr`, `ss`, `LENGTH (bs:byte list)`]
    bytes_snapshot_result_natural_memory) >> impl_tac >- simp[] >> DISCH_TAC >>
  asm_rewrite_tac [] >>
  mp_tac (Q.SPECL [`other_tv`, `other_v`, `other_offset`,
    `w2n (memory_snapshot_addr id ss)`, `w2n (src_addr:bytes32)`,
    `32 + contractABI$ceil32 (LENGTH (bs:byte list))`, `ss`] mcopy_preserves_memory_value_rel) >>
  impl_tac >- (conj_tac >- simp[] >> conj_tac >- simp[] >> decide_tac) >> simp[]
QED
