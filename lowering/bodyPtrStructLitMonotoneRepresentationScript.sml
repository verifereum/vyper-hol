Theory bodyPtrStructLitMonotoneRepresentation
Ancestors robustCopyTransportPtr

(* Shrinking taint only strengthens the adversary's agreement obligation. *)
Theorem copied_window_agree_witness_mono:
  !tn tn' mem mem' src dst n m.
    mem_bytes_at dst n mem' = mem_bytes_at src n mem /\
    (!i. i < n ==> (dst+i IN tn' ==> src+i IN tn)) /\
    mem_agree_outside tn' mem' m ==>
    ?mix. mem_agree_outside tn mem mix /\
          mem_bytes_at src n mix = mem_bytes_at dst n m
Proof
  rpt gen_tac >> strip_tac >>
  `!i. i < n /\ dst+i IN tn' ==> src+i IN tn` by metis_tac[] >>
  qspecl_then [`tn`, `tn'`, `mem`, `mem'`, `src`, `dst`, `n`, `m`]
    MATCH_MP_TAC copied_window_decreasing_taint_witness >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem robust_val_in_memory_copy_transport_mono:
  !tv v src dst n tn tn' mem mem'.
    val_wf tv v /\ val_footprint tv v <= n /\
    mem_bytes_at dst n mem' = mem_bytes_at src n mem /\
    (!i. i < n ==> (dst+i IN tn' ==> src+i IN tn)) /\
    (!m. mem_agree_outside tn mem m ==> val_in_memory tv v src m) ==>
    !m. mem_agree_outside tn' mem' m ==> val_in_memory tv v dst m
Proof
  rpt gen_tac >> strip_tac >>
  `!i. i < n /\ dst+i IN tn' ==> src+i IN tn` by metis_tac[] >>
  qspecl_then [`tv`, `v`, `src`, `dst`, `n`, `tn`, `tn'`, `mem`, `mem'`]
    MATCH_MP_TAC robust_val_in_memory_decreasing_taint_transport >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
