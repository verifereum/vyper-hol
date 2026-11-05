(* Typed representations at clean decoder endpoints. *)
Theory calldataTypedRobustPtr
Ancestors calldataDecodePtr robustCopyTransportPtr exprSimMemoryTransport
  bodyPtrDefs venomMemProofs list valueEncoding valueEncodingProofs valueEncodingProps

Theorem clean_footprint_val_in_memory_robust:
  !tv v p mem tainted.
    val_wf tv v /\ val_in_memory tv v p mem /\
    (!i. p <= i /\ i < p + val_footprint tv v ==> i NOTIN tainted) ==>
    !mem'. mem_agree_outside tainted mem mem' ==>
      val_in_memory tv v p mem'
Proof
  rpt strip_tac >> irule val_in_memory_relocate_footprint >>
  conj_tac >- simp[] >>
  qexistsl_tac [`mem`, `p`] >> simp[] >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `j < val_footprint tv v` >>
  `p+j NOTIN tainted` by (first_x_assum irule >> decide_tac) >>
  `mem_bytes_at (p+j) 1 mem = mem_bytes_at (p+j) 1 mem'` by
    metis_tac[mem_agree_outside_def] >>
  pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED
