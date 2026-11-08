Theory bodyPtrIfExpStorageExit
Ancestors bodyPtrIfExpStorageInvariant bodyPtrIfExpStorageSupplier
  slotCopyExecution valueEncoding valueEncodingProps venomState
  words pred_set

Theorem ifexp_copy_prefix_words:
  slot_copy_prefix load sBase p (w2n d) n t ==>
  !j. j < n ==>
    mem_word_at (w2n d+32*j) t.vs_memory =
    lookup_storage (p+n2w j)
      (if load = SLOAD then contract_storage sBase else contract_transient sBase)
Proof
  simp[slot_copy_prefix_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  `32 <= LENGTH (DROP (w2n d+32*j) t.vs_memory)` by simp[] >>
  simp[mem_word_at_def, listTheory.TAKE_APPEND1, slot_copy_word_def,
       sload_def, tload_def] >>
  Cases_on `load = SLOAD` >> gvs[]
QED

Theorem ifexp_copy_ptr_exit:
  ifexp_copy_ptr_inv ce cx rty es sa s0 G0 tn0 ee
    cs load src (Var out) sBase GBase tnBase p d n
    {(j,k) | (p+n2w j,k) IN source_taint} n t G tn /\
  type_slot_size ty <= n /\ well_formed_type_value ty /\
  slots_in_range st (w2n p) ty /\ decode_value st (w2n p) ty = SOME v /\
  storage_range_agree st
    (if load = SLOAD then contract_storage sBase else contract_transient sBase) p ty /\
  (!k b. w2n p <= w2n k /\ w2n k < w2n p+type_slot_size ty /\
    b < 32 /\ (k,b) IN source_taint ==>
    dead_bytes (if load = SLOAD then contract_storage sBase else contract_transient sBase)
      (w2n p) ty (w2n k) b) ==>
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory ty v (w2n d) m) /\
  ptr_covers G tn out t (32*n) /\ ghost_inv rty ce cx ee G tn t /\
  ghost_kept ce es sa G0 tn0 s0 G tn
Proof
  strip_tac >>
  fs[ifexp_copy_ptr_inv_def, slot_copy_inv_def] >>
  rpt strip_tac >> irule ifexp_range_storage_decode_robust >>
  conj_tac >- simp[] >>
  qexistsl_tac [`tn.t_mem`, `t.vs_memory`,
    `if load = SLOAD then contract_storage sBase else contract_transient sBase`,
    `source_taint`, `st`, `p`] >>
  simp[] >>
  drule ifexp_copy_prefix_words >> simp[] >> strip_tac >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED
