Theory bodyPtrIntCallArgPersistence
Ancestors bodyPtrDefs ptrDiscipline venomInst finite_map
  robustCopyTransportPtr exprSimProps loweringPosts venomState venomMemProofs
  valueEncoding valueEncodingProps valueEncodingProofs list arithmetic

Theorem intcall_ptr_buf_transport:
  ptr_buf_ok cenv e op G s /\
  eval_operand op t = eval_operand op s /\ op_prov H op = op_prov G op ==>
  ptr_buf_ok cenv e op H t
Proof
  Cases_on `op` >> simp[ptr_buf_ok_def, op_prov_def] >> metis_tac[]
QED

Theorem intcall_ptr_word_transport:
  is_word_type ty /\ ptr_val_ok cx ty v op G tn s /\
  op_taint un op = op_taint tn op /\ op_prov H op = op_prov G op ==>
  ptr_val_ok cx ty v' op H un t
Proof
  simp[ptr_val_ok_def]
QED

Theorem intcall_preserved_window_witness[local]:
  mem_bytes_at off n mem' = mem_bytes_at off n mem /\
  (!i. off <= i /\ i < off+n /\ i IN tn' ==> i IN tn) /\
  mem_agree_outside tn' mem' m ==>
  ?mix. mem_agree_outside tn mem mix /\
        mem_bytes_at off n mix = mem_bytes_at off n m
Proof
  strip_tac >>
  qabbrev_tac `s = (ARB:venom_state) with vs_memory := mem` >>
  qabbrev_tac `mix =
    (write_memory_with_expansion off (mem_bytes_at off n m) s).vs_memory` >>
  `mem_bytes_at off n mix = mem_bytes_at off n m` by
    (qspecl_then [`off`, `mem_bytes_at off n m`, `s`] mp_tac
       write_memory_mem_bytes_at_same >> simp[Abbr `mix`]) >>
  qexists_tac `mix` >> simp[] >>
  simp[mem_agree_outside_def] >> rpt strip_tac >>
  Cases_on `off <= i /\ i < off+n`
  >- (`i-off < n /\ off+(i-off) = i` by decide_tac >>
      `i NOTIN tn'` by metis_tac[] >>
      `EL (i-off) (mem_bytes_at off n mix) =
       EL (i-off) (mem_bytes_at off n m)` by simp[] >>
      `EL (i-off) (mem_bytes_at off n mem') =
       EL (i-off) (mem_bytes_at off n mem)` by simp[] >>
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

Theorem intcall_robust_preserved_window:
  val_wf tv v /\ val_footprint tv v <= n /\
  mem_bytes_at off n mem' = mem_bytes_at off n mem /\
  (!i. off <= i /\ i < off+n /\ i IN tn' ==> i IN tn) /\
  (!m. mem_agree_outside tn mem m ==> val_in_memory tv v off m) ==>
  !m. mem_agree_outside tn' mem' m ==> val_in_memory tv v off m
Proof
  rpt strip_tac >> drule_all intcall_preserved_window_witness >>
  disch_then (qx_choose_then `mix` strip_assume_tac) >>
  `val_in_memory tv v off mix` by metis_tac[] >>
  irule val_in_memory_footprint_agree >> simp[] >> qexists_tac `mix` >> simp[] >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `j < val_footprint tv v` >>
  `j < n` by decide_tac >>
  `EL j (mem_bytes_at off n mix) = EL j (mem_bytes_at off n m)` by simp[] >>
  gvs[EL_mem_bytes_at]
QED

Theorem intcall_fresh_argument_robust:
  vv_post ctx fn ce cx e es sa sb s es' res vv t /\
  ghost_kept ce es sa G tn s H un /\
  FLOOKUP s.vs_allocas aid = SOME (b,n) /\ aid < sa.cs_next_id /\
  (!id lb lsz. local_region ce es.scopes s id lb lsz ==>
                 b+n <= lb \/ lb+lsz <= b) /\
  val_wf tv v /\ val_footprint tv v <= n /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v b mem) ==>
  !mem. mem_agree_outside un.t_mem t.vs_memory mem ==>
        val_in_memory tv v b mem
Proof
  rpt strip_tac >> irule intcall_robust_preserved_window >>
  simp[] >> goal_assum (drule_at (Pat `mem_agree_outside _ _ _`)) >>
  qexistsl_tac [`s.vs_memory`, `n`, `tn.t_mem`] >> simp[] >>
  conj_tac
  >- (fs[ghost_kept_def] >> metis_tac[]) >>
  fs[vv_post_def] >> metis_tac[]
QED
