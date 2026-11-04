Theory lowerDloadPtrMCopy
Ancestors
  lowerDloadPtrMemoryRead lowerDloadPtrMemoryWrite lowerDloadPtrRel
  lowerDloadPtrAffine ptrDiscipline venomExecSemantics venomState
  codegenRel vfmTypes list rich_list pred_set arithmetic words

Theorem dload_snapshot_byte[local]:
  k < len ==>
  EL k (TAKE len (DROP src mem ++ REPLICATE len 0w)) =
    read_byte (src+k) mem
Proof
  strip_tac >>
  simp[EL_TAKE, EL_APPEND, EL_DROP, EL_REPLICATE, read_byte_def] >>
  IF_CASES_TAC >> simp[] >> IF_CASES_TAC >> gvs[]
QED

Theorem dload_memory_match_mcopy_region:
  dload_memory_match lo fs tn un s t /\
  dload_live_layout lo sf tf fs /\
  ((src = tsrc /\ src + len <= lo) \/
   (?owner id b c n d. dload_live_site fs owner id b c n /\
     src = b+d /\ tsrc = c+d /\ d+len <= n)) /\
  ((dst = tdst /\ dst + len <= lo) \/
   (?owner id b c n d. dload_live_site fs owner id b c n /\
     dst = b+d /\ tdst = c+d /\ d+len <= n)) ==>
  dload_memory_match lo fs
    (tn with t_mem := (tn.t_mem DIFF {p | dst <= p /\ p < dst+len})
      UNION {dst+k | k < len /\ src+k IN tn.t_mem})
    (un with t_mem := (un.t_mem DIFF {p | tdst <= p /\ p < tdst+len})
      UNION {tdst+k | k < len /\ tsrc+k IN un.t_mem})
    (mcopy dst src len s) (mcopy tdst tsrc len t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!k. k < len ==>
    (src+k IN tn.t_mem <=> tsrc+k IN un.t_mem) /\
    (src+k NOTIN tn.t_mem ==>
      read_byte (src+k) s.vs_memory = read_byte (tsrc+k) t.vs_memory)` by
    (match_mp_tac dload_memory_read_bytes >> metis_tac[]) >>
  `{k | k < len /\ src+k IN tn.t_mem} =
   {k | k < len /\ tsrc+k IN un.t_mem}` by
    (simp[EXTENSION] >> metis_tac[]) >>
  `{tdst+k | k < len /\ tsrc+k IN un.t_mem} =
   {tdst+k | k < len /\ src+k IN tn.t_mem}` by
    (simp[EXTENSION] >> metis_tac[ADD_COMM]) >>
  mp_tac (Q.INST
    [`bs` |-> `TAKE len (DROP src s.vs_memory ++ REPLICATE len 0w)`,
     `bt` |-> `TAKE len (DROP tsrc t.vs_memory ++ REPLICATE len 0w)`,
     `M` |-> `{k | k < len /\ src+k IN tn.t_mem}`,
     `a` |-> `dst`, `z` |-> `tdst`]
    (SPEC_ALL dload_memory_match_masked_write_region)) >>
  simp[LENGTH_TAKE_EQ, SUBSET_DEF, dload_snapshot_byte, mcopy_def] >>
  metis_tac[ADD_COMM]
QED
