(* Counted staging-copy facts, independent of source-language scope insertion. *)
Theory annAssignPtrScratch
Ancestors
 annAssignPtrCopy annAssignPtrSetup robustCopyTransportPtr valueEncodingProps
 valueEncoding venomMemProofs ptrDiscipline pred_set arithmetic
 bodyPtrDefs stmtSimProps exprSimProps localPtrsProps compileEnv venomState
 finite_map loweringPosts exprLoweringProps

Theorem annassign_copy_taint_window_ptr:
 !old new a b k.
 new = (old DIFF {i | b <= i /\ i < b+k}) UNION
       {b+i | i < k /\ a+i IN old} ==>
 (!i. i < k ==> (b+i IN new <=> a+i IN old)) /\
 (!i. ~(b <= i /\ i < b+k) ==> (i IN new <=> i IN old))
Proof
 rpt gen_tac >> strip_tac >> gvs[] >>
 rpt strip_tac >> eq_tac >> strip_tac >> gvs[] >> decide_tac
QED

Theorem annassign_static_copy_memory_window_ptr:
 !k a b s mem.
 mem = (if k = 0 then s.vs_memory else (mcopy b a k s).vs_memory) ==>
 mem_bytes_at b k mem = mem_bytes_at a k s.vs_memory /\
 (!i. ~(b <= i /\ i < b+k) ==>
   mem_bytes_at i 1 mem = mem_bytes_at i 1 s.vs_memory)
Proof
 rpt gen_tac >> strip_tac >> Cases_on `k = 0` >> gvs[]
 >- simp[mem_bytes_at_def] >>
 conj_tac >- simp[mcopy_mem_bytes_at_same] >>
 rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac
QED

Theorem annassign_counted_copy_robust_ptr:
 !D ctx func PG G tn s dst src a b k sa sb tv v.
 compile_copy_memory (Var dst) (Var src) k sa = ((),sb) /\
 fn_has_code sa sb func /\
 s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ k < dimword (:256) /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 ptr_covers G tn src s k /\ ptr_covers G tn dst s k /\
 val_wf tv v /\ val_footprint tv v <= k /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n a) m) ==>
 ?s' tn'. gas_path_ptr D 0 ctx func PG G tn s 0 G tn' (OK s') /\
 s'.vs_current_bb = sb.cs_current_bb /\
 s'.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~s'.vs_halted /\
 (s' with <|vs_memory := s.vs_memory;vs_inst_idx := s.vs_inst_idx|>) = s /\
 (tn' with t_mem := tn.t_mem) = tn /\
 (!x. lookup_var x s' = lookup_var x s) /\
 tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
 tn'.t_trans = tn.t_trans /\
 mem_bytes_at (w2n b) k s'.vs_memory = mem_bytes_at (w2n a) k s.vs_memory /\
 (!i. i < k ==> (w2n b+i IN tn'.t_mem <=> w2n a+i IN tn.t_mem)) /\
 (!i. ~(w2n b <= i /\ i < w2n b+k) ==>
   mem_bytes_at i 1 s'.vs_memory = mem_bytes_at i 1 s.vs_memory /\
   (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
 (!m. mem_agree_outside tn'.t_mem s'.vs_memory m ==>
      val_in_memory tv v (w2n b) m)
Proof
 rpt gen_tac >> strip_tac >>
 drule_all annassign_compile_copy_path_ptr >>
 disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
 drule annassign_static_copy_memory_window_ptr >> strip_tac >>
 drule annassign_copy_taint_window_ptr >> strip_tac >>
 qpat_x_assum `s'.vs_memory = _` kall_tac >>
 qpat_x_assum `tn'.t_mem = _` kall_tac >>
 qexistsl [`s'`,`tn'`] >> simp[] >>
 rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
 conj_tac >- simp[] >>
 qexistsl [`s.vs_memory`,`s'.vs_memory`,`k`,`w2n a`,`tn.t_mem`,`tn'.t_mem`] >>
 asm_rewrite_tac[]
QED

Theorem annassign_coverage_var_frame_ptr:
 !G tn tn' s s' p k.
 tn'.t_var = tn.t_var /\ lookup_var p s' = lookup_var p s /\
 ptr_covers G tn p s k ==> ptr_covers G tn' p s' k
Proof
 simp[ptr_covers_def, op_taint_def]
QED

Theorem annassign_ghost_exterior_ptr:
 !ctx func cenv cx es d G tn s mem mt idx writes.
 stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
 (!name b sz. local_region cenv es.scopes s name b sz ==>
    !i. b <= i /\ i < b+sz ==> i NOTIN writes) /\
 (!i. i NOTIN writes ==> mem_bytes_at i 1 mem = mem_bytes_at i 1 s.vs_memory) /\
 (!i. i NOTIN writes ==> (i IN mt <=> i IN tn.t_mem)) ==>
 ghost_inv d cenv cx es G (tn with t_mem := mt)
   (s with <|vs_memory := mem;vs_inst_idx := idx|>)
Proof
 rpt gen_tac >> strip_tac >>
 `local_ptrs_rel func cenv es.scopes s` by
   fs[stmt_state_rel_def, state_rel_def] >>
 fs[ghost_inv_def] >> conj_tac
 >- (rpt gen_tac >> strip_tac >>
     `?w. lookup_var p s = SOME w /\ val_wf entry.type entry.value /\
          type_memory_size entry.type <= sz` by
       (qpat_assum `local_ptrs_rel _ _ _ _`
          (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
        qpat_x_assum `!name entry p sz. _ ==> ?w. _` drule_all >>
        strip_tac >> metis_tac[]) >>
     `local_region cenv es.scopes s name (w2n w) sz` by
       (simp[local_region_def] >> metis_tac[]) >>
     qpat_x_assum `!name entry p sz. _` drule_all >> strip_tac >>
     conj_tac >- fs[ptr_covers_def, op_taint_def, lookup_var_def] >>
     rpt gen_tac >> strip_tac >> gvs[lookup_var_def] >>
     irule robust_val_in_memory_exterior_frame >>
     conj_tac >- simp[] >>
     qexistsl [`s.vs_memory`,`mem`,`tn.t_mem`,`mt`,`writes`] >> simp[] >>
     rpt strip_tac >>
     `val_footprint entry.type entry.value <= sz` by
       (drule val_footprint_le >> decide_tac) >>
     qpat_x_assum `!name b sz. local_region _ _ _ _ _ _ ==> _` drule >>
     disch_then (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
 fs[return_buf_ptr_def, ptr_covers_def, stor_taint_ok_def, op_taint_def,
    lookup_var_def] >>
 Cases_on `d` >- simp[return_buf_ptr_def] >>
 PairCases_on `x` >> gvs[return_buf_ptr_def, ptr_covers_def, op_taint_def,
                        lookup_var_def]
QED

Theorem annassign_state_restore_elim_ptr:
 !s s'. (s' with <|vs_memory := s.vs_memory;vs_inst_idx := s.vs_inst_idx|>) = s ==>
 s' = (s with <|vs_memory := s'.vs_memory;vs_inst_idx := s'.vs_inst_idx|>)
Proof
 rpt gen_tac >> disch_then (SUBST1_TAC o SYM) >> simp[]
QED

Theorem annassign_taint_restore_elim_ptr:
 !tn tn'. (tn' with t_mem := tn.t_mem) = tn ==>
 tn' = (tn with t_mem := tn'.t_mem)
Proof
 rpt gen_tac >> disch_then (SUBST1_TAC o SYM) >> simp[]
QED

Theorem annassign_alloca_copy_ghost_ptr:
 !ctx func cenv cx es d G tn s s' tn' inst p b sz k.
 fn_inst_ids_distinct func /\
 stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
 MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
 inst.inst_outputs = [p] /\ not_local_ptr cenv es.scopes p /\
 FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\ k <= sz /\
 (s' with <|vs_memory := s.vs_memory;vs_inst_idx := s.vs_inst_idx|>) = s /\
 (tn' with t_mem := tn.t_mem) = tn /\
 (!i. ~(b <= i /\ i < b+k) ==>
    mem_bytes_at i 1 s'.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
 (!i. ~(b <= i /\ i < b+k) ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) ==>
 ghost_inv d cenv cx es G tn' s'
Proof
 rpt gen_tac >> strip_tac >>
 drule annassign_state_restore_elim_ptr >> disch_tac >>
 drule annassign_taint_restore_elim_ptr >> disch_tac >>
 `alloca_inv s /\ local_ptrs_rel func cenv es.scopes s` by
   fs[stmt_state_rel_def, state_rel_def] >>
 qpat_assum `s' = _` (fn th => once_rewrite_tac[th]) >>
 qpat_assum `tn' = _` (fn th => once_rewrite_tac[th]) >>
 irule annassign_ghost_exterior_ptr >> simp[] >>
 reverse conj_tac >- metis_tac[] >>
 qexists `{i | b <= i /\ i < b+k}` >> simp[] >>
 rpt gen_tac >> strip_tac >>
 drule_all local_ptrs_rel_alloca_disjoint >>
 simp[regions_disjoint_def] >> decide_tac
QED
