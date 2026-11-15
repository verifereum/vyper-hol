Theory dftPacketCommonOracle
Ancestors
  dftGasFromListReplayBoundary dftGasFromListTraceDefs list alist

Theorem dft_packet_lookup_overlap:
  !keys slots vals.
    LIST_REL (\key slot. slot = ALOOKUP obs key) keys slots /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots vals ==>
    EVERY (\(key,w). ALOOKUP obs key = NONE \/
      ALOOKUP obs key = SOME w) (ZIP (keys,vals))
Proof
  Induct >> Cases_on `slots` >> Cases_on `vals` >> simp[] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem dft_packet_common_oracle:
  ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT keys /\
  LIST_REL (\key slot. slot = ALOOKUP obs key) keys slots /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots vals /\
  dftGasFromListTraceDefs$trace_gas source = ZIP (keys,vals) /\
  EVERY (\kw. MEM kw obs) (dftGasFromListTraceDefs$trace_gas target) ==>
  dftGasFromListTraceDefs$trace_agrees
    (\key. case ALOOKUP (obs ++ ZIP (keys,vals)) key of
      NONE => 0w | SOME w => w) source /\
  dftGasFromListTraceDefs$trace_agrees
    (\key. case ALOOKUP (obs ++ ZIP (keys,vals)) key of
      NONE => 0w | SOME w => w) target
Proof
  strip_tac >> irule trace_agrees_lookup_fill >> simp[] >>
  conj_tac >- metis_tac[LIST_REL_LENGTH] >>
  metis_tac[dft_packet_lookup_overlap]
QED
