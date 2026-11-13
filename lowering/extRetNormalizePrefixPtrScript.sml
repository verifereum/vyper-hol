Theory extRetNormalizePrefixPtr
Ancestors
  robustCopyTransportPtr valueEncoding valueEncodingProofs valueEncodingProps
  exprSimMemoryTransport arithmetic pred_set

(* Half-open slots: a zero stride makes the access premise impossible. *)
Theorem normalize_array_slot_in_parent:
  !a stride j n k len.
    j < n /\ len <= stride /\
    a+j*stride <= k /\ k < a+j*stride+len ==>
    a <= k /\ k < a+n*stride
Proof
  rpt strip_tac >>
  `SUC j <= n` by decide_tac >>
  `SUC j * stride <= n * stride` by
    (irule LESS_MONO_MULT >> simp[]) >>
  pop_assum mp_tac >> pure_rewrite_tac [MULT_CLAUSES] >> decide_tac
QED

Theorem normalize_array_slot_before:
  !b stride j i k len.
    j < i /\ len <= stride /\
    b+j*stride <= k /\ k < b+j*stride+len ==>
    k < b+i*stride
Proof
  rpt strip_tac >>
  `SUC j <= i` by decide_tac >>
  `SUC j * stride <= i * stride` by
    (irule LESS_MONO_MULT >> simp[]) >>
  pop_assum mp_tac >> pure_rewrite_tac [MULT_CLAUSES] >> decide_tac
QED

(* The effects may change taint arbitrarily INSIDE the current destination
   slot. No claim of clean padding, or equality of source/destination strides,
   is needed to preserve the robust representations outside that slot. *)
Theorem normalize_array_robust_prefix_advance:
  !i n a b ss ds stv sv dtv dv tn tn' mem mem' writes.
    i < n /\
    (a+n*ss <= b \/ b+n*ds <= a) /\
    (!k. k IN writes ==> b+i*ds <= k /\ k < b+(i+1)*ds) /\
    (!k. k NOTIN writes ==> mem_bytes_at k 1 mem' = mem_bytes_at k 1 mem) /\
    (!k. k NOTIN writes ==> (k IN tn' <=> k IN tn)) /\
    (!j. i < j /\ j < n ==>
      val_wf (stv j) (sv j) /\ val_footprint (stv j) (sv j) <= ss /\
      (!m. mem_agree_outside tn mem m ==>
        val_in_memory (stv j) (sv j) (a+j*ss) m)) /\
    (!j. j < i ==>
      val_wf (dtv j) (dv j) /\ val_footprint (dtv j) (dv j) <= ds /\
      (!m. mem_agree_outside tn mem m ==>
        val_in_memory (dtv j) (dv j) (b+j*ds) m)) /\
    (!m. mem_agree_outside tn' mem' m ==>
      val_in_memory (dtv i) (dv i) (b+i*ds) m) ==>
    (!j m. i < j /\ j < n /\ mem_agree_outside tn' mem' m ==>
      val_in_memory (stv j) (sv j) (a+j*ss) m) /\
    (!j m. j < i+1 /\ mem_agree_outside tn' mem' m ==>
      val_in_memory (dtv j) (dv j) (b+j*ds) m)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- (rpt strip_tac >>
      irule robust_val_in_memory_exterior_frame >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`mem`, `mem'`, `tn`, `tn'`, `writes`] >> simp[] >>
      rpt strip_tac >>
      `a <= i' /\ i' < a+n*ss` by
        (irule normalize_array_slot_in_parent >>
         qexistsl_tac [`j`, `val_footprint (stv j) (sv j)`] >>
         simp[]) >>
      `b+i*ds <= i' /\ i' < b+(i+1)*ds` by metis_tac[] >>
      `b <= i' /\ i' < b+n*ds` by
        (irule normalize_array_slot_in_parent >>
         qexistsl_tac [`i`, `ds`] >>
         simp[LEFT_ADD_DISTRIB] >> decide_tac) >>
      decide_tac) >>
  rpt strip_tac >> Cases_on `j = i` >- gvs[] >>
  `j < i` by decide_tac >>
  irule robust_val_in_memory_exterior_frame >>
  conj_tac >- metis_tac[] >>
      qexistsl_tac [`mem`, `mem'`, `tn`, `tn'`, `writes`] >> simp[] >>
  rpt strip_tac >>
  `i' < b+i*ds` by
    (irule normalize_array_slot_before >>
     qexistsl_tac [`j`, `val_footprint (dtv j) (dv j)`] >>
     simp[]) >>
  metis_tac[NOT_LESS]
QED
