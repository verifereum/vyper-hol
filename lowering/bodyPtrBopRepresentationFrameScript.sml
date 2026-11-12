Theory bodyPtrBopRepresentationFrame
Ancestors
  robustCopyTransportPtr bodyPtrDefs venomMemProofs valueEncodingProofs list exprSimMemoryTransport

Theorem bop_window_agree_witness:
  !taint taint' mem mem' p n m.
    mem_bytes_at p n mem' = mem_bytes_at p n mem /\
    (!i. p <= i /\ i < p+n /\ i IN taint' ==> i IN taint) /\
    mem_agree_outside taint' mem' m ==>
    ?mix. mem_agree_outside taint mem mix /\
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
      `i NOTIN taint'` by metis_tac[] >>
      `EL (i-p) (mem_bytes_at p n mix) =
       EL (i-p) (mem_bytes_at p n m)` by simp[] >>
      `EL (i-p) (mem_bytes_at p n mem') =
       EL (i-p) (mem_bytes_at p n mem)` by simp[] >>
      `mem_bytes_at i 1 mem' = mem_bytes_at i 1 m` by
        metis_tac[mem_agree_outside_def] >>
      `EL 0 (mem_bytes_at i 1 mem') = EL 0 (mem_bytes_at i 1 m)` by simp[] >>
      gvs[EL_mem_bytes_at] >>
      irule LIST_EQ >> simp[EL_mem_bytes_at] >> metis_tac[]) >>
  sym_tac >> simp[Abbr `mix`] >>
  irule EQ_TRANS >> qexists_tac `mem_bytes_at i 1 s.vs_memory` >>
  conj_tac
  >- (irule write_memory_mem_bytes_at_disjoint >> simp[] >> decide_tac) >>
  simp[Abbr `s`]
QED

Theorem bop_robust_representation_frame:
  !tv v p taint taint' mem mem'.
    val_wf tv v /\
    mem_bytes_at p (val_footprint tv v) mem' =
      mem_bytes_at p (val_footprint tv v) mem /\
    (!i. p <= i /\ i < p + val_footprint tv v /\ i IN taint' ==> i IN taint) /\
    (!m. mem_agree_outside taint mem m ==> val_in_memory tv v p m) ==>
    !m. mem_agree_outside taint' mem' m ==> val_in_memory tv v p m
Proof
  rpt strip_tac >> drule_all bop_window_agree_witness >>
  disch_then (qx_choose_then `mix` strip_assume_tac) >>
  `val_in_memory tv v p mix` by metis_tac[] >>
  irule val_in_memory_relocate_footprint >>
  conj_tac >- simp[] >>
  qexistsl_tac [`mix`, `p`] >> simp[]
QED

Theorem bop_ptr_mem_ok_frame:
  ptr_mem_ok cx ty v op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  eval_operand op s' = eval_operand op s /\
  (!x. op = Var x ==> FLOOKUP G' x = FLOOKUP G x) /\
  (!w. eval_operand op s = SOME w ==>
    mem_bytes_at (w2n w) (val_footprint tv v) s'.vs_memory =
      mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\
         i IN tn'.t_mem ==> i IN tn.t_mem)) ==>
  ptr_mem_ok cx ty v op G' tn' s'
Proof
  simp[ptr_mem_ok_def] >> rpt strip_tac
  >- (irule bop_robust_representation_frame >>
      simp[] >> qexistsl_tac [`s.vs_memory`, `s'.vs_memory`, `tn.t_mem`, `tn'.t_mem`] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem bop_ptr_val_ok_frame:
  ptr_val_ok cx ty v op G tn s /\
  eval_operand op s' = eval_operand op s /\
  op_taint tn' op = op_taint tn op /\
  (is_word_type ty ==> op_prov G' op = NONE) /\
  (~is_word_type ty ==>
    evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
    (!x. op = Var x ==> FLOOKUP G' x = FLOOKUP G x) /\
    (!w. eval_operand op s = SOME w ==>
      mem_bytes_at (w2n w) (val_footprint tv v) s'.vs_memory =
        mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
      (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\
           i IN tn'.t_mem ==> i IN tn.t_mem))) ==>
  ptr_val_ok cx ty v op G' tn' s'
Proof
  simp[ptr_val_ok_def] >> strip_tac >> simp[] >> strip_tac >>
  irule bop_ptr_mem_ok_frame >> metis_tac[]
QED
