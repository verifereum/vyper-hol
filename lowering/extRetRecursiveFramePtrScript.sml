Theory extRetRecursiveFramePtr
Ancestors
  extRetRecursiveResourcePtr extRetScratchResourcePtr bodyPtrDefs
  bodyPtrBopInMachineMemory valueEncodingProps abiStaticAggregateProps
  venomState venomMemDefs ptrDiscipline finite_map pred_set arithmetic

Definition encoder_scratch_span_def:
  encoder_scratch_span sites s =
    {i | ?id b n. id IN sites /\ FLOOKUP s.vs_allocas id = SOME (b,n) /\
                  b <= i /\ i < b+n}
End

Definition encoder_write_envelope_def:
  encoder_write_envelope sites s dst cap =
    {i | dst <= i /\ i < dst+cap} UNION encoder_scratch_span sites s
End

Theorem encoder_memory_frame_union:
  mem_agree_outside first m1 m0 /\ mem_agree_outside second m2 m1 ==>
  mem_agree_outside (first UNION second) m2 m0
Proof
  simp[mem_agree_outside_def] >> metis_tac[]
QED

Theorem encoder_taint_frame_union:
  (!i. i NOTIN first ==> (i IN tm1 <=> i IN tm0)) /\
  (!i. i NOTIN second ==> (i IN tm2 <=> i IN tm1)) ==>
  !i. i NOTIN first UNION second ==> (i IN tm2 <=> i IN tm0)
Proof
  simp[] >> metis_tac[]
QED

Theorem encoder_memory_frame_mono:
  mem_agree_outside small m1 m0 /\ small SUBSET large ==>
  mem_agree_outside large m1 m0
Proof
  simp[mem_agree_outside_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem encoder_envelope_protected:
  encoder_resource ctx fn sites q len protected s /\ MEM (id,p,n) protected /\
  regions_disjoint (p,n) (dst,cap) ==>
  !i. p <= i /\ i < p+n ==> i NOTIN encoder_write_envelope sites s dst cap
Proof
  strip_tac >> drule_all encoder_resource_protected >> strip_tac >>
  gen_tac >> strip_tac >>
  simp[encoder_write_envelope_def, encoder_scratch_span_def] >>
  conj_tac >- (fs[regions_disjoint_def] >> decide_tac) >>
  rpt gen_tac >> strip_tac >> spose_not_then strip_assume_tac >>
  `n <> 0` by decide_tac >>
  fs[scratch_resource_def] >>
  `regions_disjoint (p,n) (b,n')` by metis_tac[] >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem encoder_frame_clean_word:
  mem_agree_outside writes sf.vs_memory s.vs_memory /\
  (!i. i NOTIN writes ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN writes) /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) ==>
  mload p sf = mload p s /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >> conj_tac >-
    (`mem_bytes_at p 32 sf.vs_memory = mem_bytes_at p 32 s.vs_memory` by
       (irule mem_agree_outside_window >> metis_tac[]) >>
     metis_tac[mem_word_at_eq_mload, mem_word_at_bytes]) >>
  metis_tac[]
QED
