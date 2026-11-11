(* Counted staging-copy facts, independent of source-language scope insertion. *)
Theory annAssignPtrScratch
Ancestors
 annAssignPtrCopy annAssignPtrSetup robustCopyTransportPtr valueEncodingProps
 valueEncoding valueEncodingDefs venomMemProofs ptrDiscipline pred_set arithmetic
 bodyPtrDefs stmtSimProps exprSimProps localPtrsProps compileEnv loweringStateRelDefs venomState
 finite_map loweringPosts exprLoweringProps exprSimBufferStore venomExecSemantics venomMemDefs
 allocationPtr annAssignPtrAllocGhost

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
 s'.vs_memory = (if k = 0 then s.vs_memory else
                   (mcopy (w2n b) (w2n a) k s).vs_memory) /\
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
 qpat_x_assum `tn'.t_mem = _` kall_tac >>
 `!m. mem_agree_outside tn'.t_mem s'.vs_memory m ==>
      val_in_memory tv v (w2n b) m` by
   (qpat_x_assum `s'.vs_memory = _` kall_tac >>
    rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
    conj_tac >- simp[] >>
    qexistsl [`s.vs_memory`,`s'.vs_memory`,`k`,`w2n a`,`tn.t_mem`,`tn'.t_mem`] >>
    asm_rewrite_tac[]) >>
 qexistsl [`s'`,`tn'`] >> simp[]
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
    mem_bytes_at i 1 s'.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tn'.t_mem <=> i IN tn.t_mem)) ==>
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
 simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem annassign_alloca_copy_state_ptr:
 !ctx func cenv cx es s s' inst p b a sz k.
 stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
 MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
 inst.inst_outputs = [p] /\ not_local_ptr cenv es.scopes p /\
 FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\ k <= sz /\
 (s' with <|vs_memory := s.vs_memory;vs_inst_idx := s.vs_inst_idx|>) = s /\
 s'.vs_memory = (if k = 0 then s.vs_memory else (mcopy b a k s).vs_memory) ==>
 stmt_state_rel ctx func cenv cx es s'
Proof
 rpt gen_tac >> strip_tac >>
 drule annassign_state_restore_elim_ptr >> disch_tac >>
 Cases_on `k = 0` >> gvs[]
 >- (`s' = s with vs_inst_idx := s'.vs_inst_idx` by
       (qpat_x_assum `s' = _` (fn th => once_rewrite_tac[th]) >>
        simp[venom_state_component_equality]) >>
     metis_tac[stmt_state_rel_inst_idx]) >>
 `stmt_state_rel ctx func cenv cx es (mcopy b a k s)` by
   (irule stmt_state_rel_mcopy_alloca >> metis_tac[]) >>
 `mcopy b a k s = s with vs_memory := (mcopy b a k s).vs_memory` by
   simp[mcopy_def, write_memory_with_expansion_def,
        venom_state_component_equality] >>
 `s' = mcopy b a k s with vs_inst_idx := s'.vs_inst_idx` by
   (qpat_x_assum `s' = _` (fn th => once_rewrite_tac[th]) >>
    simp[mcopy_def, write_memory_with_expansion_def,
         venom_state_component_equality]) >>
 metis_tac[stmt_state_rel_inst_idx]
QED

Theorem annassign_ghost_kept_exterior_ptr:
 !cenv es sa G0 tn0 s0 G tn tn' writes.
 ghost_kept cenv es sa G0 tn0 s0 G tn /\ tn'.t_var = tn.t_var /\
 (!i. i NOTIN writes ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
 (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < sa.cs_next_id /\ off <= i /\ i < off+sz ==> i NOTIN writes) /\
 (!n b sz i. local_region cenv es.scopes s0 n b sz /\
    b <= i /\ i < b+sz ==> i NOTIN writes) ==>
 ghost_kept cenv es sa G0 tn0 s0 G tn'
Proof
 rw[ghost_kept_def, op_taint_def] >> metis_tac[]
QED

Theorem annassign_alloca_copy_kept_ptr:
 !ctx func cenv cx es sa G0 tn0 s0 G tn s tn' inst p b sz k.
 stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
 MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\
 not_local_ptr cenv es.scopes p /\
 FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\ k <= sz /\
 sa.cs_next_id <= inst.inst_id /\
 (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
              FLOOKUP s.vs_allocas aid = SOME entry) /\
 (!n lo nsz. local_region cenv es.scopes s0 n lo nsz ==>
              local_region cenv es.scopes s n lo nsz) /\
 ghost_kept cenv es sa G0 tn0 s0 G tn /\ tn'.t_var = tn.t_var /\
 (!i. ~(b <= i /\ i < b+k) ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) ==>
 ghost_kept cenv es sa G0 tn0 s0 G tn'
Proof
 rpt gen_tac >> strip_tac >>
 `alloca_inv s /\ local_ptrs_rel func cenv es.scopes s` by
   fs[stmt_state_rel_def, state_rel_def] >>
 irule annassign_ghost_kept_exterior_ptr >>
 qexistsl [`tn`,`{i | b <= i /\ i < b+k}`] >> simp[] >> reverse conj_tac
 >- (rpt gen_tac >> strip_tac >>
     `FLOOKUP s.vs_allocas aid = SOME (off,sz')` by metis_tac[] >>
     `aid <> inst.inst_id` by decide_tac >>
     fs[alloca_inv_def, allocas_non_overlapping_def] >>
     first_x_assum (qspecl_then [`aid`,`inst.inst_id`,`off`,`sz'`,`b`,`sz`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
 rpt gen_tac >> strip_tac >>
 `local_region cenv es.scopes s n b' sz'` by metis_tac[] >>
 drule_all local_ptrs_rel_alloca_disjoint >>
 simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED


Theorem annassign_allocated_static_copy_ptr:
 !ctx func cenv cx es d PG G0 tn0 s0 sa G tn s dst src a b k st st1 tv v inst sz.
 compile_copy_memory (Var dst) (Var src) k st = ((),st1) /\
 fn_has_code st st1 func /\ fn_inst_ids_distinct func /\
 s.vs_current_bb = st.cs_current_bb /\
 s.vs_inst_idx = LENGTH st.cs_current_insts /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ k < dimword (:256) /\
 stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
 ghost_kept cenv es sa G0 tn0 s0 G tn /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 ptr_covers G tn src s k /\ ptr_covers G tn dst s sz /\
 val_wf tv v /\ val_footprint tv v <= k /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n a) m) /\
 MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
 inst.inst_outputs = [dst] /\ not_local_ptr cenv es.scopes dst /\
 FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n b,sz) /\ k <= sz /\
 sa.cs_next_id <= inst.inst_id /\
 (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
              FLOOKUP s.vs_allocas aid = SOME entry) /\
 (!n lo nsz. local_region cenv es.scopes s0 n lo nsz ==>
              local_region cenv es.scopes s n lo nsz) ==>
 ?s' tn'. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 G tn' (OK s') /\
 stmt_state_rel ctx func cenv cx es s' /\ ghost_inv d cenv cx es G tn' s' /\
 ghost_kept cenv es sa G0 tn0 s0 G tn' /\ ptr_covers G tn' dst s' sz /\
 s'.vs_current_bb = st1.cs_current_bb /\
 s'.vs_inst_idx = LENGTH st1.cs_current_insts /\ ~s'.vs_halted /\
 (!x. lookup_var x s' = lookup_var x s) /\
 s'.vs_allocas = s.vs_allocas /\
 (!m. mem_agree_outside tn'.t_mem s'.vs_memory m ==> val_in_memory tv v (w2n b) m)
Proof
 rpt gen_tac >> strip_tac >>
 `ptr_covers G tn dst s k` by
   (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS]) >>
 drule_all annassign_counted_copy_robust_ptr >>
 disch_then (qspecl_then [`cx_dead cx`,`PG`] strip_assume_tac) >>
 `ghost_inv d cenv cx es G tn' s'` by
   (qpat_x_assum `s'.vs_memory = _` kall_tac >>
    drule_at (Pat `stmt_state_rel _ _ _ _ _ _`) annassign_alloca_copy_ghost_ptr >>
    disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
    disch_then (drule_at (Pat `_.inst_outputs = _`)) >>
    disch_then (drule_at (Pat `(_ with <|vs_memory := _;vs_inst_idx := _|>) = _`)) >>
    disch_then (drule_at (Pat `(_ with t_mem := _) = _`)) >>
    disch_then irule >> simp[] >> qexists `k` >> simp[]) >>
 `ghost_kept cenv es sa G0 tn0 s0 G tn'` by
   (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`) annassign_alloca_copy_kept_ptr >>
    disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
    disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _.inst_id = SOME _`)) >>
    disch_then (drule_at (Pat `_.inst_outputs = _`)) >>
    disch_then (drule_at (Pat `_.t_var = _`)) >>
    disch_then irule >> simp[] >> qexists `k` >> simp[] >>
    rpt strip_tac >> metis_tac[]) >>
 `stmt_state_rel ctx func cenv cx es s'` by
   (irule annassign_alloca_copy_state_ptr >> metis_tac[]) >>
 `ptr_covers G tn' dst s' sz` by
   (irule annassign_coverage_var_frame_ptr >> metis_tac[]) >>
 qexistsl [`s'`,`tn'`] >> simp[] >>
 qpat_x_assum `(_ with <|vs_memory := _;vs_inst_idx := _|>) = _` mp_tac >>
 simp[venom_state_component_equality]
QED

(* expr_val_at, not ghost coverage alone, supplies the frontier argument.
   Its bytewise form also handles an empty value at an arbitrary address. *)
Theorem annassign_alloca_expr_robust_ptr:
 !ctx func cenv cx t sa sb es v op s tv w id n out u tn.
 stmt_state_rel ctx func cenv cx es s /\
 expr_val_at cenv cx t sa sb es v op s /\
 evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
 eval_operand op s = SOME w /\ val_wf tv v /\
 MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
 n < dimword (:256) /\
 step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m) ==>
 !m. mem_agree_outside
   (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_mem
   u.vs_memory m ==> val_in_memory tv v (w2n w) m
Proof
 rpt gen_tac >> strip_tac >>
 drule_all annassign_alloca_effects_ptr >>
 disch_then (qspecl_then [`[]`,`FEMPTY`,`tn`] strip_assume_tac) >>
 rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
 conj_tac >- simp[] >>
 qexistsl [`s.vs_memory`,`u.vs_memory`,`tn.t_mem`,
   `(step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_mem`,
   `{i | s.vs_alloca_next <= i}`] >> simp[] >>
 rpt strip_tac >> drule_all expr_val_at_below_frontier >> decide_tac
QED

Theorem annassign_alloca_source_transport_ptr:
 !ctx func cenv cx t sa sb es v src s tv w id n out u PG G tn k.
 stmt_state_rel ctx func cenv cx es s /\
 expr_val_at cenv cx t sa sb es v (Var src) s /\
 evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
 lookup_var src s = SOME w /\ src <> out /\ val_wf tv v /\
 ptr_covers G tn src s k /\
 MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
 n < dimword (:256) /\
 step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m) ==>
 lookup_var src u = SOME w /\
 ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
   (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) src u k /\
 (!m. mem_agree_outside
   (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_mem
   u.vs_memory m ==> val_in_memory tv v (w2n w) m)
Proof
 rpt gen_tac >> strip_tac >> conj_tac
 >- (drule_all annassign_alloca_effects_ptr >>
     disch_then (qspecl_then [`PG`,`G`,`tn`] strip_assume_tac) >>
     first_x_assum (qspec_then `src` mp_tac) >> simp[]) >>
 conj_tac
 >- (irule alloca_step_old_ptr_covers >> simp[] >> metis_tac[]) >>
 drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`) annassign_alloca_expr_robust_ptr >>
 disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
 disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
 simp[eval_operand_def] >> disch_then (qspec_then `tn` mp_tac) >> simp[]
QED
