(* Local robustness needs no new taint in the window, not global taint equality. *)
Theory bodyPtrBytestringBuiltinsWindowGhost
Ancestors
  robustCopyTransportPtr exprSimPtrLiteralBuffer exprSimProps bodyPtrDefs
  compileEnv venomMemProofs venomState valueEncodingProofs list pred_set
  finite_map words exprSimMemoryTransport

Theorem same_window_agree_witness:
  mem_bytes_at b len mem' = mem_bytes_at b len mem /\
  (!i. b <= i /\ i < b + len /\ i IN dirty' ==> i IN dirty) /\
  mem_agree_outside dirty' mem' m ==>
  ?mix. mem_agree_outside dirty mem mix /\
    mem_bytes_at b len mix = mem_bytes_at b len m
Proof
  strip_tac >>
  `!i. i < len ==> (b+i IN (dirty UNION dirty') <=> b+i IN dirty)` by
    (rpt strip_tac >>
     `b <= b+i /\ b+i < b+len` by decide_tac >>
     simp[] >> metis_tac[]) >>
  `mem_agree_outside (dirty UNION dirty') mem' m` by
    (fs[mem_agree_outside_def] >> metis_tac[]) >>
  drule_all copied_window_agree_witness >> simp[]
QED

Theorem robust_val_in_memory_window_transport:
  val_wf tv v /\ val_footprint tv v <= len /\
  mem_bytes_at b len mem' = mem_bytes_at b len mem /\
  (!i. b <= i /\ i < b+len /\ i IN dirty' ==> i IN dirty) /\
  (!m. mem_agree_outside dirty mem m ==> val_in_memory tv v b m) ==>
  !m. mem_agree_outside dirty' mem' m ==> val_in_memory tv v b m
Proof
  rpt strip_tac >> drule_all same_window_agree_witness >>
  disch_then (qx_choose_then `mix` strip_assume_tac) >>
  `val_in_memory tv v b mix` by metis_tac[] >>
  irule val_in_memory_relocate_footprint >>
  conj_tac >- simp[] >> qexistsl_tac [`mix`,`b`] >> simp[] >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `i < val_footprint tv v` >>
  `i < len` by decide_tac >>
  `EL i (mem_bytes_at b len mix) = EL i (mem_bytes_at b len m)` by simp[] >>
  gvs[EL_mem_bytes_at]
QED

Theorem ghost_inv_local_window_transport:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_rel fn cenv es.scopes s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x s' = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
  (!name b len. local_region cenv es.scopes s name b len ==>
    mem_bytes_at b len s'.vs_memory = mem_bytes_at b len s.vs_memory /\
    (!i. b <= i /\ i < b+len /\ i IN tm.t_mem ==> i IN tn.t_mem)) /\
  stor_taint_ok cx tm s' ==>
  ghost_inv d cenv cx es H tm s'
Proof
  strip_tac >>
  `!x sz. not_fresh_at sa x /\ ptr_covers G tn x s sz ==>
    ptr_covers H tm x s' sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      conj_tac >- metis_tac[] >>
      rpt gen_tac >> strip_tac >>
      `lookup_var p s = SOME w` by metis_tac[] >>
      `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
        (fs[local_ptrs_rel_def] >> metis_tac[]) >>
      `val_footprint entry.type entry.value <= sz` by
        (drule val_footprint_le >> decide_tac) >>
      `local_region cenv es.scopes s name (w2n w) sz` by
        (simp[local_region_def] >> metis_tac[]) >>
      qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >> strip_tac >>
      `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory entry.type entry.value (w2n w) m` by metis_tac[] >>
      drule_all robust_val_in_memory_window_transport >>
      simp[])
  >- (Cases_on `d` >> fs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME bc)` >> PairCases_on `bc` >>
      fs[return_buf_ptr_def] >> metis_tac[]) >>
  metis_tac[]
QED
