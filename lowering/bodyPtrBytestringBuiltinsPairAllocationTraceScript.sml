Theory bodyPtrBytestringBuiltinsPairAllocationTrace
Ancestors bodyPtrBytestringBuiltinsAllocationTrace

Theorem allocation_trace_pair:
  !s p k.
    allocation_trace s (SND p) /\
    (!v t. allocation_trace t (SND (k v t))) ==>
    allocation_trace s (SND (UNCURRY k p))
Proof
  rpt gen_tac >> PairCases_on `p` >> simp[] >>
  metis_tac[allocation_trace_trans]
QED
