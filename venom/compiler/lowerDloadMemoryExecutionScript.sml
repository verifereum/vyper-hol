Theory lowerDloadMemoryExecution
Ancestors
  lowerDloadPairedBoundary venomExecSemantics lowerDloadRelocation lowerDloadOperand
  ptrDiscipline venomMemProps venomState list rich_list pred_set

Theorem ld_mload_byte[local]:
  k < 32 ==>
  [EL k (word_to_bytes (mload a s) T)] = read_memory (a+k) 1 s
Proof
  strip_tac >>
  `word_to_bytes (mload a s) T =
    TAKE 32 (DROP a s.vs_memory ++ REPLICATE 32 0w)` by
    (simp[mload_def] >> irule word_bytes_roundtrip_256 >>
     simp[LENGTH_TAKE_EQ]) >>
  simp[read_memory_def, EL_TAKE, EL_APPEND_EQN, EL_DROP,
       LENGTH_DROP, EL_REPLICATE] >>
  Cases_on `a+k < LENGTH s.vs_memory` >>
  simp[DROP_EQ_NIL, TAKE1, HD_DROP, HD_APPEND_NOT_NIL] >>
  `DROP (a+k) s.vs_memory = []` by (simp[DROP_EQ_NIL] >> decide_tac) >>
  simp[] >> EVAL_TAC
QED

Theorem ld_mload_masked:
  ld_byte_rel R Ts Tt (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  (!k. k < 32 ==> R (a+k) (b+k)) ==>
  ld_mask_word (mem_word_taint Ts a) (mem_word_taint Tt b)
    (mload a s) (mload b t)
Proof
  simp[ld_byte_rel_def] >> strip_tac >>
  simp[ld_mask_word_def, mem_word_taint_def, SUBSET_DEF] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `read_memory (a+k) 1 s = read_memory (b+k) 1 t` by metis_tac[] >>
  metis_tac[ld_mload_byte, CONS_11]
QED
