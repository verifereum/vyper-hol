Theory bodyPtrPopArraySupport
Ancestors bodyPtrPopRepresentationSupport exprSimAggregateEncoding
  bodyPtrPopSpatialSplit typedCopyPtr valueEncoding valueEncodingProofs bodyPtrDefs
  pred_set list arithmetic

Theorem pop_support_elems_agreement:
  (!j. j < LENGTH vs ==> pop_rep_support tv (EL j vs)
    (a+j*type_memory_size tv) (supp j)) /\
  (!j i. j < LENGTH vs /\ i IN supp j ==>
    mem_bytes_at i 1 m = mem_bytes_at i 1 n) ==>
  (elems_in_memory vs a tv m <=> elems_in_memory vs a tv n)
Proof
  strip_tac >> eq_tac >> strip_tac >> irule elems_in_memory_intro >>
  rpt strip_tac >>
  `val_in_memory tv (EL i vs) (a+i*type_memory_size tv) m <=>
   val_in_memory tv (EL i vs) (a+i*type_memory_size tv) n` by
    (fs[pop_rep_support_def] >> metis_tac[]) >>
  metis_tac[elems_in_memory_EL]
QED

Theorem pop_support_dynarray:
  (!j. j < LENGTH vs ==> pop_rep_support tv (EL j vs)
    (a+32+j*type_memory_size tv) (supp j)) ==>
  pop_rep_support (ArrayTV tv bd) (ArrayV (DynArrayV vs)) a
    ({i | a <= i /\ i < a+32} UNION BIGUNION {supp j | j < LENGTH vs})
Proof
  strip_tac >> simp[pop_rep_support_def] >> rpt strip_tac >>
  `mem_word_at a m = mem_word_at a n` by
    (irule pop_clean_word_agreement >>
     qexists_tac `{i | ~(a <= i /\ i < a+32)}` >>
     simp[bodyPtrDefsTheory.mem_agree_outside_def] >> metis_tac[]) >>
  `elems_in_memory vs (a+32) tv m <=> elems_in_memory vs (a+32) tv n` by
    (irule pop_support_elems_agreement >> qexists_tac `supp` >> simp[] >>
     metis_tac[]) >>
  simp[val_in_memory_def]
QED

Theorem pop_support_empty_dynarray:
  pop_rep_support (ArrayTV tv bd) (ArrayV (DynArrayV [])) a
    {i | a <= i /\ i < a+32}
Proof
  mp_tac (Q.INST [`vs` |-> `[]`, `supp` |-> `(\j. {}):num -> num set`]
    pop_support_dynarray) >> simp[]
QED

Theorem pop_support_dynarray_split:
  (!j. j < LENGTH (pre ++ [last]) ==> pop_rep_support tv (EL j (pre ++ [last]))
    (a+32+j*type_memory_size tv) (supp j)) ==>
  pop_rep_support (ArrayTV tv bd) (ArrayV (DynArrayV pre)) a
    ({i | a <= i /\ i < a+32} UNION BIGUNION {supp j | j < LENGTH pre}) /\
  pop_rep_support tv last (a+32+LENGTH pre*type_memory_size tv) (supp (LENGTH pre))
Proof
  strip_tac >> conj_tac
  >- (irule pop_support_dynarray >> rpt strip_tac >>
      first_x_assum (qspec_then `j` mp_tac) >> simp[listTheory.EL_APPEND_EQN]) >>
  first_x_assum (qspec_then `LENGTH pre` mp_tac) >> simp[listTheory.EL_APPEND_EQN]
QED

(* This is a conditional frame, not an assertion that every owner's support
   misses a selected header. Reachability must establish that classification. *)
Theorem pop_support_dynarray_header_frame:
  (!j. j < LENGTH vs ==> pop_rep_support tv (EL j vs)
    (a+32+j*type_memory_size tv) (supp j)) /\
  DISJOINT ({i | a <= i /\ i < a+32} UNION BIGUNION {supp j | j < LENGTH vs})
    {i | off <= i /\ i < off+32} /\
  (!m. mem_agree_outside dirty s.vs_memory m ==>
    val_in_memory (ArrayTV tv bd) (ArrayV (DynArrayV vs)) a m) /\
  t = ((mstore off w s) with vs_inst_idx := SUC s.vs_inst_idx) ==>
  !m. mem_agree_outside dirty t.vs_memory m ==>
    val_in_memory (ArrayTV tv bd) (ArrayV (DynArrayV vs)) a m
Proof
  strip_tac >> rpt strip_tac >> irule pop_rep_support_robust_frame >>
  qexistsl_tac [`t.vs_memory`, `s.vs_memory`, `dirty`,
    `{i | a <= i /\ i < a+32} UNION BIGUNION {supp j | j < LENGTH vs}`,
    `{i | off <= i /\ i < off+32}`] >>
  simp[] >> reverse conj_tac
  >- (irule pop_support_dynarray >> simp[]) >>
  gvs[] >> mp_tac (Q.SPECL [`s`,`off`,`w`] typedCopyPtrTheory.mstore_memory_frame) >>
  simp[mem_agree_outside_def] >> metis_tac[]
QED
