(* Byte-list observations of the safety-only memory projection. *)
Theory lowerDloadSafetyBytes
Ancestors
  lowerDloadSafetyKernel venomState codegenRel list rich_list arithmetic
    finite_map pred_set regularCallEmitSim byte ptrDiscipline venomMemProps
    lowerDloadSafetyValues

Theorem ld_read_memory_byte:
  j < n ==> EL j (read_memory off n s) = read_byte (off+j) s.vs_memory
Proof
  strip_tac >> simp[read_memory_def, read_byte_def] >>
  `j < LENGTH (DROP off s.vs_memory ++ REPLICATE n 0w)` by simp[] >>
  simp[EL_TAKE] >>
  Cases_on `off+j < LENGTH s.vs_memory`
  >- (simp[EL_APPEND1, EL_DROP] >> decide_tac) >>
  simp[EL_APPEND2, EL_REPLICATE]
QED

Theorem ld_read_memory_length[simp]:
  LENGTH (read_memory off n s) = n
Proof
  simp[read_memory_def]
QED

Theorem ld_memory_read_low:
  ld_memory lo A tn s t /\ off+n <= lo /\
  (!j. j < n ==> off+j NOTIN tn.t_mem) ==>
  read_memory off n s = read_memory off n t
Proof
  strip_tac >> irule LIST_EQ >> simp[ld_read_memory_byte] >>
  rpt strip_tac >> irule ld_memory_low >>
  qexistsl_tac [`A`, `lo`, `tn`] >> simp[] >> decide_tac
QED

Theorem ld_memory_read_slot:
  ld_memory lo A tn s t /\ FLOOKUP A k = SOME (b,c,sz) /\
  delta+n <= sz /\ (!j. j < n ==> b+delta+j NOTIN tn.t_mem) ==>
  read_memory (b+delta) n s = read_memory (c+delta) n t
Proof
  strip_tac >> irule LIST_EQ >> simp[ld_read_memory_byte] >>
  rpt strip_tac >>
  simp[GSYM ADD_ASSOC] >> irule ld_memory_slot >>
  goal_assum (drule_at Any) >> qexistsl_tac [`lo`, `tn`] >>
  gvs[GSYM ADD_ASSOC] >> decide_tac
QED

Theorem ld_memory_read_low_masked:
  ld_memory lo A tn s t /\ off+n <= lo /\ j < n /\
  off+j NOTIN tn.t_mem ==>
  EL j (read_memory off n s) = EL j (read_memory off n t)
Proof
  strip_tac >> simp[ld_read_memory_byte] >>
  irule ld_memory_low >> qexistsl_tac [`A`, `lo`, `tn`] >>
  gvs[ADD_COMM] >> decide_tac
QED

Theorem ld_memory_read_slot_masked:
  ld_memory lo A tn s t /\ FLOOKUP A k = SOME (b,c,sz) /\
  delta+n <= sz /\ j < n /\ b+delta+j NOTIN tn.t_mem ==>
  EL j (read_memory (b+delta) n s) = EL j (read_memory (c+delta) n t)
Proof
  strip_tac >> simp[ld_read_memory_byte, GSYM ADD_ASSOC] >>
  irule ld_memory_slot >> goal_assum (drule_at Any) >>
  qexistsl_tac [`lo`, `tn`] >> gvs[GSYM ADD_ASSOC] >> decide_tac
QED

Theorem ld_memory_transport:
  !lo A tn s t coords tn' s' t'.
  ld_memory lo A tn s t /\
  (!i. i < lo /\ i NOTIN tn'.t_mem ==>
    if i IN coords then read_byte i s'.vs_memory = read_byte i t'.vs_memory
    else i NOTIN tn.t_mem /\
      read_byte i s'.vs_memory = read_byte i s.vs_memory /\
      read_byte i t'.vs_memory = read_byte i t.vs_memory) /\
  (!k b c n j. FLOOKUP A k = SOME (b,c,n) /\ j < n /\
    b+j NOTIN tn'.t_mem ==>
    if b+j IN coords then
      read_byte (b+j) s'.vs_memory = read_byte (c+j) t'.vs_memory
    else b+j NOTIN tn.t_mem /\
      read_byte (b+j) s'.vs_memory = read_byte (b+j) s.vs_memory /\
      read_byte (c+j) t'.vs_memory = read_byte (c+j) t.vs_memory) ==>
  ld_memory lo A tn' s' t'
Proof
  rpt gen_tac >> strip_tac >> simp[ld_memory_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!i. _` (qspec_then `i` mp_tac) >>
      simp[] >> Cases_on `i IN coords` >> simp[] >>
      metis_tac[ld_memory_low]) >>
  rpt strip_tac >>
  qpat_x_assum `!k b c n j. _` drule >>
  disch_then (qspecl_then [`j`] mp_tac) >>
  simp[] >> Cases_on `b+j IN coords` >> simp[] >>
  metis_tac[ld_memory_slot]
QED

Theorem ld_mstore_byte:
  read_byte i (mstore off v s).vs_memory =
  if off <= i /\ i < off + 32 then EL (i-off) (word_to_bytes v T)
  else read_byte i s.vs_memory
Proof
  `mstore off v s = write_memory_with_expansion off (word_to_bytes v T) s` by
    simp[mstore_def, write_memory_with_expansion_def, LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  simp[read_byte_write_memory_with_expansion, LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem ld_mstore_masked_byte:
  word_agree_except mask v w /\ j < 32 /\ j NOTIN mask ==>
  read_byte (off+j) (mstore off v s).vs_memory =
  read_byte (dst+j) (mstore dst w t).vs_memory
Proof
  simp[ld_mstore_byte, word_agree_except_def] >> metis_tac[]
QED

Theorem ld_mload_masked:
  (!j. j < 32 /\ j NOTIN mask ==>
    EL j (read_memory off 32 s) = EL j (read_memory dst 32 t)) ==>
  word_agree_except mask (mload off s) (mload dst t)
Proof
  `!off s. mload off s = word_of_bytes T (0w:bytes32) (read_memory off 32 s)` by
    simp[mload_def, read_memory_def] >>
  simp[word_agree_except_def, word_bytes_roundtrip_256]
QED

Theorem ld_memory_mload_low:
  ld_memory lo A tn s t /\ off+32 <= lo ==>
  word_agree_except {j | j < 32 /\ off+j IN tn.t_mem}
    (mload off s) (mload off t)
Proof
  strip_tac >> irule ld_mload_masked >> simp[] >> rpt strip_tac >>
  irule ld_memory_read_low_masked >> simp[] >>
  qexistsl_tac [`A`, `lo`, `tn`] >> simp[ADD_COMM]
QED

Theorem ld_memory_mload_slot:
  ld_memory lo A tn s t /\ FLOOKUP A k = SOME (b,c,sz) /\ delta+32 <= sz ==>
  word_agree_except {j | j < 32 /\ b+delta+j IN tn.t_mem}
    (mload (b+delta) s) (mload (c+delta) t)
Proof
  strip_tac >> irule ld_mload_masked >> simp[] >> rpt strip_tac >>
  irule ld_memory_read_slot_masked >> simp[] >>
  qexistsl_tac [`A`, `k`, `lo`, `sz`, `tn`] >> simp[GSYM ADD_ASSOC]
QED

Theorem ld_memory_mload_access:
  access_ok lo (ld_erase A o_f H) fn inst s /\
  ~in_revert_forward fn s /\ mem_read_ops inst = SOME ops /\
  MEM (w2n x,32) (source_memory_read_ranges inst s) /\
  (op_prov H ops.iao_ofst = NONE ==> x = y) /\
  (!a. op_prov H ops.iao_ofst = SOME a ==> ld_wordrel A (SOME a) x y) /\
  (!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword (:256)) /\
  ld_memory lo A tn s t ==>
  word_agree_except (mem_word_taint tn.t_mem (w2n x))
    (mload (w2n x) s) (mload (w2n y) t)
Proof
  strip_tac >>
  `0 < (32:num)` by simp[] >>
  drule_all ld_read_access_cases >> strip_tac
  >- (gvs[mem_word_taint_def] >> once_rewrite_tac[ADD_COMM] >> irule ld_memory_mload_low >> metis_tac[]) >>
  gvs[mem_word_taint_def] >> rewrite_tac[ADD_ASSOC] >> irule ld_memory_mload_slot >> metis_tac[]
QED
