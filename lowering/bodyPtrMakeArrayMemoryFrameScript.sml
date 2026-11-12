(* Window framing permits taint to shrink during child evaluation. *)
Theory bodyPtrMakeArrayMemoryFrame
Ancestors
  robustCopyTransportPtr representationCleanPtr exprSimMemoryTransport
  valueEncoding valueEncodingProofs valueEncodingProps bodyPtrDefs
  venomMemProofs list arithmetic

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
