(* Byte-list observations of the safety-only memory projection. *)
Theory lowerDloadSafetyBytes
Ancestors
  lowerDloadSafetyKernel venomState codegenRel list rich_list arithmetic
  finite_map pred_set

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
