(* TOP-LEVEL: complete word layouts contain exactly their source ABI bytes.
   Total zero-extended reads remove the old encoder lemma's memory-list
   length premise. Helper: base layouts survive appending zero bytes. *)
Theory memoryValueAbiWord
Ancestors
  valueEncodingDefs memoryValueDefs abiEncoderProps valueEncoding valueEncodingProofs
  vyperABI vyperTyping compileEnv contractABI list rich_list arithmetic words

Theorem val_in_memory_base_append_zero:
  !bt v offset mem count.
    val_in_memory (BaseTV bt) v offset (mem ++ REPLICATE count 0w) <=>
      val_in_memory (BaseTV bt) v offset mem
Proof
  rpt gen_tac >> Cases_on `v` >>
  simp[val_in_memory_def, mem_word_at_append_zero, mem_bytes_at_append_zero] >>
  rename1 `val_in_memory (BaseTV bt) (ArrayV av) _ _` >>
  Cases_on `av` >> simp[val_in_memory_def]
QED

Theorem memory_value_rel_base_abi:
  !bt v offset mem av.
    memory_value_rel (BaseTV bt) v offset mem /\
    is_word_type (BaseT bt) /\ value_has_type (BaseTV bt) v /\
    vyper_to_abi_base bt v = SOME av ==>
    mem_bytes_at offset 32 mem = enc (vyper_base_to_abi_type bt) av
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`bt`, `v`, `offset`, `mem ++ REPLICATE (offset + 32) 0w`, `av`]
    val_in_memory_prim_enc) >> impl_tac
  >- (simp[val_in_memory_base_append_zero] >> fs[memory_value_rel_def]) >>
  simp[mem_bytes_at_append_zero]
QED

Theorem memory_value_rel_flag_abi:
  !flag_width k offset mem.
    memory_value_rel (FlagTV flag_width) (FlagV k) offset mem ==>
    mem_bytes_at offset 32 mem = enc (Uint 256) (NumV k)
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`flag_width`, `k`, `offset`, `mem ++ REPLICATE (offset + 32) 0w`]
    val_in_memory_flag_enc) >> impl_tac
  >- (simp[val_in_memory_def, mem_word_at_append_zero] >>
      fs[memory_value_rel_def, val_in_memory_def]) >>
  simp[mem_bytes_at_append_zero]
QED
