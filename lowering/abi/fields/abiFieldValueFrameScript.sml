(* TOP-LEVEL: a written-window frame preserves previously evaluated typed
   arguments whose complete memory representations avoid every write. *)
Theory abiFieldValueFrame
Ancestors
  abiMemoryFrame memoryValueFrame memoryReadProps memoryLayoutDefs valueEncoding
  compileEnv venomState list pair arithmetic

Theorem abi_memory_frame_value:
  !tv v offset writes before after.
    memory_value_rel tv v offset before.vs_memory /\ val_wf tv v /\
    abi_memory_frame writes before after /\
    EVERY (\(base,write_len). abi_window_separated offset (type_memory_size tv) base write_len) writes ==>
    memory_value_rel tv v offset after.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`writes`, `before`, `after`, `offset`, `type_memory_size tv`] abi_memory_frame_read) >>
  impl_tac >- (conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tv`, `v`, `offset`, `before.vs_memory`, `after.vs_memory`]
    memory_value_rel_mem_agree) >> impl_tac >- fs[read_memory_eq_mem_bytes_at] >> simp[]
QED

Theorem abi_memory_frame_value_region:
  !tv v offset byte_count writes before after.
    memory_value_rel tv v offset before.vs_memory /\ val_wf tv v /\ type_memory_size tv <= byte_count /\
    abi_memory_frame writes before after /\
    EVERY (\(base,write_len). abi_window_separated offset byte_count base write_len) writes ==>
    memory_value_rel tv v offset after.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`writes`, `before`, `after`, `offset`, `byte_count`] abi_memory_frame_read) >>
  impl_tac >- (conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tv`, `v`, `offset`, `byte_count`, `before.vs_memory`, `after.vs_memory`]
    memory_value_rel_mem_agree_region) >>
  impl_tac >- fs[read_memory_eq_mem_bytes_at] >> simp[]
QED
