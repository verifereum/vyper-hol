Theory exprSimAbiDecodeSiteTransport
Ancestors
  exprSimAbiDecodeSiteProvenance abiDecoderFrame venomState
  finite_map pred_set arithmetic list

Theorem abi_decode_alloc_progress_frontier:
  abi_decode_alloc_progress sites s t /\ B+cnt <= s.vs_alloca_next ==>
  B+cnt <= t.vs_alloca_next
Proof
  simp[abi_decode_alloc_progress_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem abi_decode_alloc_progress_source:
  abi_decode_alloc_progress sites s t /\ B+cnt <= s.vs_alloca_next /\
  (!id b sz. id IN sites /\ FLOOKUP s.vs_allocas id = SOME(b,sz) ==>
    abi_footprint_disjoint B cnt [(b,sz)]) ==>
  !id b sz. id IN sites /\ FLOOKUP t.vs_allocas id = SOME(b,sz) ==>
    abi_footprint_disjoint B cnt [(b,sz)]
Proof
  simp_tac bool_ss [abi_decode_alloc_progress_def] >> rpt strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (fs[abi_footprint_disjoint_def] >> metis_tac[LESS_EQ_TRANS]) >>
  PairCases_on `x` >> metis_tac[optionTheory.SOME_11]
QED

Theorem abi_decode_site_writes_shrink:
  abi_decode_alloc_progress sites s t ==>
  abi_decode_site_writes sites d outsz t SUBSET
  abi_decode_site_writes sites d outsz s
Proof
  simp_tac bool_ss [abi_decode_alloc_progress_def] >> strip_tac >>
  simp[abi_decode_site_writes_def, SUBSET_DEF] >> rpt strip_tac
  >- metis_tac[LESS_EQ_TRANS]
  >- metis_tac[LESS_EQ_TRANS] >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- metis_tac[LESS_EQ_TRANS] >>
  PairCases_on `x'` >> metis_tac[optionTheory.SOME_11]
QED

Theorem abi_decode_site_writes_final:
  abi_decode_alloc_progress sites s t ==>
  abi_decode_site_writes sites d outsz s SUBSET
  ({a | d <= a /\ a < d+outsz} UNION {a | s.vs_alloca_next <= a} UNION
   {a | ?id b sz. id IN sites /\ FLOOKUP t.vs_allocas id = SOME(b,sz) /\
      b <= a /\ a < b+sz})
Proof
  simp[abi_decode_alloc_progress_def, abi_decode_site_writes_def, SUBSET_DEF] >>
  metis_tac[]
QED
