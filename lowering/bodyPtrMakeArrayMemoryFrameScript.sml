(* Window framing permits taint to shrink during child evaluation. *)
Theory bodyPtrMakeArrayMemoryFrame
Ancestors
  robustCopyTransportPtr representationCleanPtr exprSimMemoryTransport
  valueEncoding valueEncodingProofs valueEncodingProps bodyPtrDefs
  venomMemProofs list arithmetic abiDecodeStaticProps pair


Definition literal_prefix_ok_def:
  literal_prefix_ok cells tn s <=>
    EVERY (\(tv,v,p,k). val_wf tv v /\ val_footprint tv v <= k /\
      !m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v p m) cells
End

Theorem literal_prefix_nil[simp]:
  literal_prefix_ok [] tn s
Proof
  simp[literal_prefix_ok_def]
QED

Theorem literal_prefix_append[simp]:
  literal_prefix_ok (xs ++ ys) tn s <=>
  literal_prefix_ok xs tn s /\ literal_prefix_ok ys tn s
Proof
  simp[literal_prefix_ok_def, EVERY_APPEND]
QED

Theorem literal_prefix_cell:
  literal_prefix_ok [(tv,v,p,k)] tn s <=>
  val_wf tv v /\ val_footprint tv v <= k /\
  !m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v p m
Proof
  simp[literal_prefix_ok_def]
QED

Theorem literal_prefix_lookup:
  literal_prefix_ok cells tn s /\ MEM (tv,v,p,k) cells ==>
  val_wf tv v /\ val_footprint tv v <= k /\
  !m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v p m
Proof
  simp[literal_prefix_ok_def, EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED

Theorem literal_prefix_transport:
  literal_prefix_ok cells tn s /\
  (!tv v p k. MEM (tv,v,p,k) cells /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v p m) ==>
    !m. mem_agree_outside tm.t_mem z.vs_memory m ==> val_in_memory tv v p m) ==>
  literal_prefix_ok cells tm z
Proof
  simp[literal_prefix_ok_def, EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED


Theorem shrinking_window_agree_witness:
  !T T' mem mem' p n m.
    mem_bytes_at p n mem' = mem_bytes_at p n mem /\
    (!i. p <= i /\ i < p+n /\ i IN T' ==> i IN T) /\
    mem_agree_outside T' mem' m ==>
    ?mix. mem_agree_outside T mem mix /\
          mem_bytes_at p n mix = mem_bytes_at p n m
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`T`, `T'`, `mem`, `mem'`, `p`, `p`, `n`, `m`]
    mp_tac copied_window_decreasing_taint_witness >>
  impl_tac >- (simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  simp[]
QED

Theorem robust_val_in_memory_shrinking_frame:
  !tv v p n T T' mem mem'.
    val_wf tv v /\ val_footprint tv v <= n /\
    mem_bytes_at p n mem' = mem_bytes_at p n mem /\
    (!i. p <= i /\ i < p+n /\ i IN T' ==> i IN T) /\
    (!m. mem_agree_outside T mem m ==> val_in_memory tv v p m) ==>
    !m. mem_agree_outside T' mem' m ==> val_in_memory tv v p m
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tv`, `v`, `p`, `p`, `n`, `T`, `T'`, `mem`, `mem'`]
    mp_tac robust_val_in_memory_decreasing_taint_transport >>
  impl_tac >- (simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  simp[]
QED

Theorem literal_prefix_store_frame:
  literal_prefix_ok cells tn s /\
  EVERY (\(tv,v,p,k). p+k <= b) cells /\
  (!i. ~(b <= i /\ i < b+n) ==>
    mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tm.t_mem <=> i IN tn.t_mem)) ==>
  literal_prefix_ok cells tm z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule literal_prefix_transport >> goal_assum (drule_at Any) >>
  rpt strip_tac >>
  `val_wf tv v /\ val_footprint tv v <= k` by metis_tac[literal_prefix_lookup] >>
  `p+k <= b` by (gvs[EVERY_MEM, FORALL_PROD] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  irule robust_val_in_memory_shrinking_frame >> simp[] >>
  qexistsl [`tn.t_mem`, `tm.t_mem`, `s.vs_memory`, `z.vs_memory`, `k`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> `~(b <= i /\ i < b+n)` by decide_tac >> metis_tac[]) >>
  irule mem_bytes_at_bytewise >> rpt strip_tac >>
  `~(b <= i /\ i < b+n)` by decide_tac >> metis_tac[]
QED
