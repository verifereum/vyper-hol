Theory abiEncodePtrEmptyGhost
Ancestors abiEncodePtrGhostFrame bodyPtrHashBuiltinsAllocFrame bodyPtrDefs
  loweringStateRelDefs localPtrsProps venomState finite_map pred_set arithmetic

Theorem abi_encode_empty_suffix_ghost:
  ghost_inv rb ce cx es Gp tp prepared /\
  local_ptrs_rel func ce es.scopes prepared /\ local_ptrs_reserved ce st /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!n b sz. local_region ce es.scopes prepared n b sz ==>
    regions_disjoint p 32 b sz) /\
  (!i. i < p \/ p+32 <= i ==>
    mem_bytes_at i 1 actual.vs_memory = mem_bytes_at i 1 prepared.vs_memory) /\
  tf.t_mem = tp.t_mem DIFF {i | p <= i /\ i < p+32} /\
  actual.vs_accounts = prepared.vs_accounts /\
  actual.vs_transient = prepared.vs_transient /\ actual.vs_call_ctx = prepared.vs_call_ctx /\
  tf.t_stor = tp.t_stor /\ tf.t_trans = tp.t_trans /\ tf.t_imm = tp.t_imm /\
  (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP Gp x /\
    op_taint tf (Var x) = op_taint tp (Var x)) /\
  (!x v. not_fresh_at st x /\ lookup_var x prepared = SOME v ==>
    lookup_var x actual = SOME v) /\
  ghost_kept ce es st G tn initial Gp tp ==>
  ghost_inv rb ce cx es H tf actual /\ ghost_kept ce es st G tn initial H tf
Proof
  strip_tac >> conj_tac
  >- (irule abi_encode_ghost_inv_exterior_defined >>
      qexistsl_tac [`Gp`, `func`, `prepared`, `st`, `tp`, `{i | p <= i /\ i < p+32}`] >>
      simp[] >> rpt conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!n b sz. _` drule >>
          simp[regions_disjoint_def] >> decide_tac) >>
      rpt strip_tac >> simp[] >>
      `i < p \/ p+32 <= i` by decide_tac >> simp[]) >>
  irule hash_ghost_kept_clean_tail >> goal_assum (drule_at Any) >>
  simp[SUBSET_DEF]
QED
