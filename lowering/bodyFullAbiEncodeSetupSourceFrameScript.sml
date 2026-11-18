Theory bodyFullAbiEncodeSetupSourceFrame
Ancestors
  typedMemoryCopy bodyPtrMakeArrayMemoryFrame
  exprSimAbiEncodeNonwordResources

Theorem abi_encode_setup_source_bytes:
  typed_copy_state_frame a (p+32) write_len s t /\
  venomMemDefs$regions_disjoint (src,cap) (p,N) /\
  (write_len = 0 \/ write_len = 32) /\ 32+write_len <= N
  ==> mem_bytes_at src cap t.vs_memory = mem_bytes_at src cap s.vs_memory
Proof
  disch_tac >> Cases_on `cap = 0`
  >- gvs[valueEncodingDefsTheory.mem_bytes_at_def] >>
  qpat_x_assum `_ /\ _` (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `0 < cap` by decide_tac >>
  drule_all abi_encode_source_method_exclusion >>
  gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem abi_encode_setup_source_robust:
  typed_copy_state_frame a (p+32) write_len s t /\
  venomMemDefs$regions_disjoint (src,val_footprint tv v) (p,N) /\
  (write_len = 0 \/ write_len = 32) /\ 32+write_len <= N /\
  val_wf tv v /\ tn'.t_mem SUBSET tn.t_mem /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v src mem)
  ==> !mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==> val_in_memory tv v src mem
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_tac >>
  irule robust_val_in_memory_shrinking_frame >> simp[] >>
  qexistsl [`tn.t_mem`, `tn'.t_mem`, `s.vs_memory`, `t.vs_memory`, `val_footprint tv v`] >>
  simp[] >> conj_tac
  >- (gvs[pred_setTheory.SUBSET_DEF]) >>
  metis_tac[GEN_ALL abi_encode_setup_source_bytes]
QED
