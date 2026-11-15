(* Exterior framing of materialized tuple resources. Tuple assembly uses
   typedCopyTuplePtr.tuple_in_memory_from_elements directly (with MAP_TAKE). *)
Theory bodyFullAbiEncodeTupleResources
Ancestors
  robustCopyTransportPtr typedCopyTuplePtr list pair

Theorem abi_encode_resources_exterior_frame:
  EVERY (\(tv,v,p).
    val_wf tv v /\
    (!i. p <= i /\ i < p + val_footprint tv v ==> i NOTIN writes) /\
    (!m. mem_agree_outside tn mem m ==> val_in_memory tv v p m)) slots /\
  (!i. i NOTIN writes ==> mem_bytes_at i 1 mem' = mem_bytes_at i 1 mem) /\
  (!i. i NOTIN writes ==> (i IN tn' <=> i IN tn)) ==>
  EVERY (\(tv,v,p).
    !m. mem_agree_outside tn' mem' m ==> val_in_memory tv v p m) slots
Proof
  Induct_on `slots` >- simp[] >>
  gen_tac >> PairCases_on `h` >> simp[] >>
  disch_then strip_assume_tac >> rpt strip_tac >>
  irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`mem`, `mem'`, `tn`, `tn'`, `writes`] >> simp[]
QED
