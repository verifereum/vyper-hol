(* Allocation changes only fresh bytes; reused sites add no memory taint. *)
Theory bodyPtrEnvBuiltinsAllocation
Ancestors allocationPtr robustCopyTransportPtr localPtrsProps bodyPtrDefs
  loweringHalt exprLoweringProps exprSimDefs exprSimProps compileEnv venomState venomInst
  venomExecSemantics venomMemDefs ptrDiscipline finite_map pred_set

Theorem alloca_step_frame_effects:
  !ctx fn cenv cx es s id n out s1 PG G tn.
    stmt_state_rel ctx fn cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
    s1.vs_memory = s.vs_memory /\
    (!i. i < s.vs_alloca_next ==>
      (i IN (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn).t_mem
       <=> i IN tn.t_mem)) /\
    (!p. p <> out ==>
      lookup_var p s1 = lookup_var p s /\
      FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1) p = FLOOKUP G p /\
      op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
      drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[update_var_def, lookup_var_def, op_taint_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> simp[] >> decide_tac) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `PG`, `G`, `tn`] strip_assume_tac) >>
  simp[update_var_def, lookup_var_def, op_taint_def, FLOOKUP_UPDATE]
QED

Theorem alloca_step_local_robust:
  !ctx fn cenv cx es s id n out s1 tn name entry p sz w.
    stmt_state_rel ctx fn cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory entry.type entry.value (w2n w) m) ==>
    !m. mem_agree_outside
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn).t_mem
      s1.vs_memory m ==> val_in_memory entry.type entry.value (w2n w) m
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_rel fn cenv es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  `val_wf entry.type entry.value /\
   w2n w + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> first_x_assum drule_all >> simp[]) >>
  `val_footprint entry.type entry.value <= type_memory_size entry.type` by
    metis_tac[val_footprint_le] >>
  drule_all alloca_step_frame_effects >>
  disch_then (qspecl_then [`[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >> simp[] >>
  qexistsl_tac [`s.vs_memory`, `s.vs_memory`, `tn.t_mem`,
    `(step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn).t_mem`,
    `{i | s.vs_alloca_next <= i}`] >> simp[] >> rpt strip_tac >>
  gvs[] >> decide_tac
QED

Theorem alloca_step_ghost_kept:
  !ctx fn cenv cx es s id n out s1 sa PG G tn.
    stmt_state_rel ctx fn cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    ~not_fresh_at sa out ==>
    ghost_kept cenv es sa G tn s
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn)
Proof
  rpt gen_tac >> strip_tac >> drule_all alloca_step_frame_effects >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  rewrite_tac[ghost_kept_def] >> conj_tac
  >- (rpt strip_tac >> `x <> out` by metis_tac[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> `i < s.vs_alloca_next` by
        (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
         qpat_x_assum `!aid base sz. FLOOKUP s.vs_allocas aid = SOME (base,sz) ==> _` drule >> decide_tac) >> metis_tac[]) >>
  rpt strip_tac >> `local_ptrs_rel fn cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `i < s.vs_alloca_next` by
    (fs[local_region_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> gvs[] >> decide_tac) >>
  metis_tac[]
QED

Theorem alloca_step_ghost_inv:
  !ctx fn d cenv cx es s id n out s1 sa PG G tn.
    stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    local_ptrs_reserved cenv sa /\ ~not_fresh_at sa out /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
    ghost_inv d cenv cx es
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) s1
Proof
  rpt gen_tac >> strip_tac >> drule_all alloca_step_frame_effects >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_def] >> strip_tac >> conj_tac
  >- suspend "locals" >>
  conj_tac >- suspend "return" >>
  conj_tac
  >- (rpt strip_tac >> `x <> out` by metis_tac[] >> metis_tac[]) >>
  drule_all alloca_step_stor_taint_ok >> simp[]
QED

Resume alloca_step_ghost_inv[locals]:
  rpt gen_tac >> strip_tac >>
  `p <> out` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `ptr_covers G tn p s sz /\
   !w mem. lookup_var p s = SOME w /\ mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem` by metis_tac[] >>
  conj_tac
  >- (drule_all alloca_step_old_ptr_covers >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  irule alloca_step_local_robust >> simp[] >> metis_tac[]
QED

Resume alloca_step_ghost_inv[return]:
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  PairCases_on `x` >> fs[return_buf_ptr_def] >>
  `x <> out` by metis_tac[] >>
  `ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) x s1 x1` by
    (drule_all alloca_step_old_ptr_covers >> simp[]) >>
  metis_tac[]
QED

Finalise alloca_step_ghost_inv

Theorem selector_alloca_local_disjoint:
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  not_local_ptr cenv es.scopes out /\ n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  lookup_var out s1 = SOME a /\ local_region cenv es.scopes s name b sz ==>
  b + sz <= w2n a \/ w2n a + n <= b
Proof
  strip_tac >>
  `local_ptrs_rel fn cenv es.scopes s /\ alloca_inv s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      drule_all stmt_state_rel_alloca_fresh_bound >> strip_tac >>
      gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      `s.vs_alloca_next < dimword (:256)` by decide_tac >>
      gvs[wordsTheory.w2n_n2w] >>
      `regions_disjoint b sz s.vs_alloca_next n` by
        (irule local_ptrs_rel_above_frontier >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      fs[compileEnvTheory.regions_disjoint_def]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `site0 < dimword (:256)` by decide_tac >> gvs[wordsTheory.w2n_n2w] >>
  `regions_disjoint site0 n b sz` by
    (irule local_ptrs_rel_alloca_disjoint >>
     qexistsl_tac [`cenv`, `fn`, `mk_inst id ALLOCA [Lit (n2w n)] [out]`,
       `name`, `out`, `es.scopes`, `s`] >> simp[mk_inst_def]) >>
  fs[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED
