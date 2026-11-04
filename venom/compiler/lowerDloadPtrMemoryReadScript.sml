Theory lowerDloadPtrMemoryRead
Ancestors
  lowerDloadPtrRel ptrDiscipline venomState venomMemProps vfmTypes codegenRel list rich_list pred_set arithmetic

Theorem dload_memory_read_bytes:
  dload_memory_match lo fs tn un s t /\
  ((a = z /\ a + len <= lo) \/
   (?owner id b c n d. dload_live_site fs owner id b c n /\
      a = b+d /\ z = c+d /\ d+len <= n)) ==>
  !k. k < len ==>
    (a+k IN tn.t_mem <=> z+k IN un.t_mem) /\
    (a+k NOTIN tn.t_mem ==>
      read_byte (a+k) s.vs_memory = read_byte (z+k) t.vs_memory)
Proof
  simp[dload_memory_match_def] >> strip_tac >> rpt strip_tac
  >- (`a+k < lo` by decide_tac >>
      qpat_x_assum `!i. i < lo ==> _` (qspec_then `a+k` mp_tac) >>
      gvs[ADD_COMM])
  >- (`a+k < lo` by decide_tac >>
      qpat_x_assum `!i. i < lo ==> _` (qspec_then `a+k` mp_tac) >>
      gvs[ADD_COMM]) >>
  `d+k < n` by decide_tac >>
  first_x_assum (qspecl_then [`owner`,`id`,`b`,`c`,`n`,`d+k`] mp_tac) >>
  `b+(d+k) = a+k /\ c+(d+k) = k+z` by decide_tac >>
  asm_rewrite_tac[] >> strip_tac >> gvs[]
QED

Theorem dload_mload_byte:
  k < 32 ==>
  EL k (word_to_bytes (mload a s) T) = read_byte (a+k) s.vs_memory
Proof
  strip_tac >>
  `word_to_bytes (mload a s) T =
    TAKE 32 (DROP a s.vs_memory ++ REPLICATE 32 0w)` by
    (irule (INST_TYPE [alpha |-> ``:256``] venomMemPropsTheory.word_of_bytes_be_inj) >>
     simp[byteTheory.LENGTH_word_to_bytes, LENGTH_TAKE_EQ,
       word_to_bytes_word_of_bytes_256, mload_def] >> EVAL_TAC) >>
  simp[EL_TAKE, EL_APPEND, EL_DROP, EL_REPLICATE, read_byte_def] >>
  IF_CASES_TAC >> simp[] >>
  IF_CASES_TAC >> gvs[]
QED

Theorem dload_memory_read_word:
  dload_memory_match lo fs tn un s t /\
  ((a = z /\ a + 32 <= lo) \/
   (?owner id b c n d. dload_live_site fs owner id b c n /\
      a = b+d /\ z = c+d /\ d+32 <= n)) ==>
  mem_word_taint tn.t_mem a = mem_word_taint un.t_mem z /\
  word_agree_except (mem_word_taint tn.t_mem a) (mload a s) (mload z t)
Proof
  disch_then (mp_tac o MATCH_MP dload_memory_read_bytes) >> strip_tac >> conj_tac
  >- (simp[mem_word_taint_def, EXTENSION] >> gen_tac >>
      Cases_on `x < 32` >> simp[] >>
      first_x_assum (qspec_then `x` mp_tac) >> simp[ADD_COMM]) >>
  simp[word_agree_except_def, mem_word_taint_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `b` mp_tac) >>
  simp[dload_mload_byte, ADD_COMM]
QED
