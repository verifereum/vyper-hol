Theory lowerDloadPtrExpansionTransport
Ancestors
  lowerDloadPtrScratchTransport lowerDloadDefs venomExecSemantics venomState
  venomMemProps list rich_list words finite_map arithmetic

Theorem dload_code_data_padded_slice:
  code_layout_valid s /\ eval_operand (Label "code_end") s = SOME e /\
  w2n (off:bytes32) + w2n e < dimword (:256) ==>
  TAKE n (DROP (w2n (off+e)) s.vs_code ++ REPLICATE n 0w) =
  TAKE n (DROP (w2n off) s.vs_data_section ++ REPLICATE n 0w)
Proof
  simp[code_layout_valid_def, eval_operand_def] >> strip_tac >> gvs[] >>
  `LENGTH prefix < dimword (:256)` by
    (fs[dimword_def] >> decide_tac) >>
  gvs[LESS_MOD] >>
  `LENGTH prefix + w2n off < dimword (:256)` by decide_tac >>
  simp[word_add_def, w2n_n2w, LESS_MOD, DROP_APPEND, ADD_COMM, DROP_LENGTH_TOO_LONG]
QED

Theorem dload_mload_written_bytes:
  LENGTH bs = 32 ==>
  mload b (write_memory_with_expansion b bs s) = word_of_bytes T (0w:bytes32) bs
Proof
  strip_tac >>
  qspecl_then [`b`,`bs`,`s`] mp_tac write_memory_with_expansion_read_self >>
  simp[mload_def, TAKE_APPEND, LENGTH_TAKE, LENGTH_DROP] >>
  strip_tac >>
  simp[LENGTH_write_memory_with_expansion, MAX_DEF] >>
  IF_CASES_TAC >> simp[] >>
  `b+32 - LENGTH s.vs_memory = 0` by decide_tac >> simp[]
QED

Theorem dload_codecopy_payload:
  code_layout_valid s /\ eval_operand (Label "code_end") s = SOME e /\
  w2n (off:bytes32) + w2n e < dimword (:256) /\
  i.inst_opcode = CODECOPY /\ i.inst_operands = [dst;src;sz] /\
  eval_operand dst s = SOME b /\ eval_operand src s = SOME (off+e) /\
  eval_operand sz s = SOME 32w /\ step_inst_base i s = OK s1 ==>
  mload (w2n b) s1 = word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n off) s.vs_data_section ++ REPLICATE 32 0w))
Proof
  strip_tac >> drule_all dload_code_data_padded_slice >>
  disch_then (qspec_then `32` assume_tac) >>
  gvs[step_inst_base_def, dimword_def] >> irule dload_mload_written_bytes >>
  simp[LENGTH_TAKE_EQ]
QED

Theorem dload_codecopy_mload_payload:
  code_layout_valid s /\ eval_operand (Label "code_end") s = SOME e /\
  w2n (off:bytes32) + w2n e < dimword (:256) /\
  i.inst_opcode = CODECOPY /\ i.inst_operands = [dst;src;sz] /\
  eval_operand dst s = SOME b /\ eval_operand src s = SOME (off+e) /\
  eval_operand sz s = SOME 32w /\ step_inst_base i s = OK s1 /\
  j.inst_opcode = MLOAD /\ j.inst_operands = [addr] /\ j.inst_outputs = [out] /\
  eval_operand addr s1 = SOME b ==>
  step_inst_base j s1 = OK (update_var out
    (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n off) s.vs_data_section ++ REPLICATE 32 0w))) s1)
Proof
  strip_tac >> drule_all dload_codecopy_payload >> strip_tac >>
  simp[step_inst_base_def, exec_read1_def]
QED
