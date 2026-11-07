Theory bodyPtrPrecompileBuiltinsObservations
Ancestors typedCopyPtr bodyPtrDefs venomState pred_set

Theorem memory_observation_mstore:
  t.vs_memory = (mstore off w s).vs_memory /\
  ~(off <= i /\ i < off + 32) ==>
  mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory
Proof
  strip_tac >>
  qspecl_then [`s`, `off`, `w`] mp_tac mstore_memory_frame >>
  simp[mem_agree_outside_def] >> metis_tac[]
QED

Theorem memory_observation_compose:
  (!i. i NOTIN A ==> mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  (!i. i NOTIN B ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 u.vs_memory) ==>
  !i. i NOTIN (A UNION B) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory
Proof
  simp[] >> metis_tac[]
QED
