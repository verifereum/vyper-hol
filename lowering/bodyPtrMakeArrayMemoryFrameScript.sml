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
  rpt strip_tac >>
  qabbrev_tac `s = (ARB:venom_state) with vs_memory := mem` >>
  qabbrev_tac `mix =
    (write_memory_with_expansion p (mem_bytes_at p n m) s).vs_memory` >>
  `mem_bytes_at p n mix = mem_bytes_at p n m` by
    (qspecl_then [`p`, `mem_bytes_at p n m`, `s`] mp_tac
       write_memory_mem_bytes_at_same >> simp[Abbr `mix`]) >>
  qexists_tac `mix` >> simp[] >>
  simp[mem_agree_outside_def] >> rpt strip_tac >>
  Cases_on `p <= i /\ i < p+n`
  >- (`i-p < n /\ p+(i-p) = i` by decide_tac >>
      `i NOTIN T'` by metis_tac[] >>
      `EL (i-p) (mem_bytes_at p n mix) =
       EL (i-p) (mem_bytes_at p n m)` by simp[] >>
      `EL (i-p) (mem_bytes_at p n mem') =
       EL (i-p) (mem_bytes_at p n mem)` by simp[] >>
      `mem_bytes_at i 1 mem' = mem_bytes_at i 1 m` by
        metis_tac[mem_agree_outside_def] >>
      `EL 0 (mem_bytes_at i 1 mem') =
       EL 0 (mem_bytes_at i 1 m)` by simp[] >>
      gvs[EL_mem_bytes_at] >>
      irule LIST_EQ >> simp[EL_mem_bytes_at] >> metis_tac[]) >>
  sym_tac >> simp[Abbr `mix`] >>
  irule EQ_TRANS >> qexists_tac `mem_bytes_at i 1 s.vs_memory` >>
  conj_tac
  >- (irule write_memory_mem_bytes_at_disjoint >> simp[] >> decide_tac) >>
  simp[Abbr `s`]
QED

Theorem robust_val_in_memory_shrinking_frame:
  !tv v p n T T' mem mem'.
    val_wf tv v /\ val_footprint tv v <= n /\
    mem_bytes_at p n mem' = mem_bytes_at p n mem /\
    (!i. p <= i /\ i < p+n /\ i IN T' ==> i IN T) /\
    (!m. mem_agree_outside T mem m ==> val_in_memory tv v p m) ==>
    !m. mem_agree_outside T' mem' m ==> val_in_memory tv v p m
Proof
  rpt strip_tac >> drule_all shrinking_window_agree_witness >>
  disch_then (qx_choose_then `mix` strip_assume_tac) >>
  `val_in_memory tv v p mix` by metis_tac[] >>
  irule val_in_memory_relocate_footprint >>
  conj_tac >- simp[] >>
  qexistsl_tac [`mix`, `p`] >> simp[] >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `i < val_footprint tv v` >>
  `i < n` by decide_tac >>
  `EL i (mem_bytes_at p n mix) = EL i (mem_bytes_at p n m)` by simp[] >>
  gvs[EL_mem_bytes_at]
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
