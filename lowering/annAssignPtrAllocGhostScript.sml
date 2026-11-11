(* Robust old-local layouts and frames across actual allocation steps. *)
Theory annAssignPtrAllocGhost
Ancestors
  allocationPtr robustCopyTransportPtr bodyPtrDefs loweringPosts loweringHalt
  venomState venomExecSemantics venomInst finite_map pred_set
  exprSimProps exprLoweringProps compileEnv loweringStateRelDefs localPtrsProps ptrDiscipline venomMemDefs

Theorem annassign_fresh_alloca_robust_ptr:
  !id n out s u tn tv v b.
    FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
    val_wf tv v /\ b + val_footprint tv v <= s.vs_alloca_next /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory tv v b m) ==>
    !m. mem_agree_outside
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_mem
      u.vs_memory m ==> val_in_memory tv v b m
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fresh_alloca_ghost >>
  disch_then (qspecl_then [`[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
  drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
  simp[] >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl [`s.vs_memory`, `s.vs_memory`, `tn.t_mem`,
    `tn.t_mem UNION {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next + n}`,
    `{i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next + n}`] >>
  gvs[update_var_def] >> rpt strip_tac >> decide_tac
QED

Theorem annassign_alloca_robust_below_frontier_ptr:
  !ctx func cenv cx es s id n out u tn tv v b.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
    val_wf tv v /\ b + val_footprint tv v <= s.vs_alloca_next /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory tv v b m) ==>
    !m. mem_agree_outside
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_mem
      u.vs_memory m ==> val_in_memory tv v b m
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (rpt strip_tac >> irule annassign_fresh_alloca_robust_ptr >>
      simp[] >> metis_tac[]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >> drule reused_alloca_memory_taint >>
  disch_then (qspecl_then [`out`, `tn`] assume_tac) >>
  gvs[update_var_def]
QED

Theorem annassign_alloca_local_robust_ptr:
  !ctx func cenv cx es s id n out u tn name entry p sz w.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory entry.type entry.value (w2n w) m) ==>
    !m. mem_agree_outside
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_mem
      u.vs_memory m ==> val_in_memory entry.type entry.value (w2n w) m
Proof
  rpt gen_tac >> strip_tac >>
  `val_wf entry.type entry.value /\
   w2n w + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
     simp[]) >>
  `w2n w + val_footprint entry.type entry.value <= s.vs_alloca_next` by
    (drule val_footprint_le >> decide_tac) >>
  rpt strip_tac >> irule annassign_alloca_robust_below_frontier_ptr >>
  simp[] >> metis_tac[]
QED

Theorem annassign_alloca_effects_ptr:
  !ctx func cenv cx es s id n out u PG G tn.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
    u.vs_memory = s.vs_memory /\
    (!q. q <> out ==>
      lookup_var q u = lookup_var q s /\
      FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u) q =
        FLOOKUP G q /\
      op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
        (Var q) = op_taint tn (Var q)) /\
    (!i. i < s.vs_alloca_next ==>
      (i IN (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_mem
       <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
      drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
      simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def] >>
      rpt strip_tac >> decide_tac) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >> drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `PG`, `G`, `tn`] strip_assume_tac) >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def]
QED

Theorem annassign_alloca_ghost_inv_ptr:
  !ctx func cenv cx es s u aid n p d PG G tn.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst aid ALLOCA [Lit (n2w n)] [p]) (fn_insts func) /\
    not_local_ptr cenv es.scopes p /\ n < dimword (:256) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> p) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> p) /\
    ghost_inv d cenv cx es G tn s /\
    step_inst_base (mk_inst aid ALLOCA [Lit (n2w n)] [p]) s = OK u ==>
    ghost_inv d cenv cx es
      (step_prov PG G (mk_inst aid ALLOCA [Lit (n2w n)] [p]) u)
      (step_taint (mk_inst aid ALLOCA [Lit (n2w n)] [p]) s u tn) u
Proof
  rpt gen_tac >> strip_tac >>
  drule_all annassign_alloca_effects_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  fs[ghost_inv_def] >> conj_tac
  >- suspend "locals" >>
  conj_tac >- suspend "return" >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  drule_all alloca_step_stor_taint_ok >> simp[]
QED

Resume annassign_alloca_ghost_inv_ptr[locals]:
  rpt gen_tac >> strip_tac >>
  `p' <> p` by (fs[not_local_ptr_def] >> metis_tac[]) >>
  conj_tac
  >- (irule alloca_step_old_ptr_covers >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  irule annassign_alloca_local_robust_ptr >> simp[] >> metis_tac[]
QED

Resume annassign_alloca_ghost_inv_ptr[return]:
  Cases_on `d` >> gvs[return_buf_ptr_def] >>
  PairCases_on `x` >> gvs[return_buf_ptr_def] >>
  irule_at Any alloca_step_old_ptr_covers >> simp[] >> metis_tac[]
QED

Finalise annassign_alloca_ghost_inv_ptr

Theorem annassign_alloca_ghost_kept_ptr:
  !ctx func cenv cx es s u aid n p sa PG G tn.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst aid ALLOCA [Lit (n2w n)] [p]) (fn_insts func) /\
    n < dimword (:256) /\ ~not_fresh_at sa p /\
    step_inst_base (mk_inst aid ALLOCA [Lit (n2w n)] [p]) s = OK u ==>
    ghost_kept cenv es sa G tn s
      (step_prov PG G (mk_inst aid ALLOCA [Lit (n2w n)] [p]) u)
      (step_taint (mk_inst aid ALLOCA [Lit (n2w n)] [p]) s u tn)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all annassign_alloca_effects_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  rewrite_tac[ghost_kept_def] >> conj_tac
  >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `off + sz <= s.vs_alloca_next` by
        (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
         metis_tac[]) >>
      `i < s.vs_alloca_next` by decide_tac >> metis_tac[]) >>
  rpt strip_tac >>
  `b + sz <= s.vs_alloca_next` by
    (fs[stmt_state_rel_def, state_rel_def, local_region_def,
        local_ptrs_rel_def] >>
     first_x_assum (qspecl_then [`n'`, `entry`, `p'`, `sz`] mp_tac) >>
     simp[]) >>
  `i < s.vs_alloca_next` by decide_tac >> metis_tac[]
QED

Theorem annassign_alloca_ghost_frame_ptr:
  !ctx func cenv cx es s u aid n p sa d PG G tn.
    stmt_state_rel ctx func cenv cx es s /\
    fn_inst_ids_distinct func /\
    MEM (mk_inst aid ALLOCA [Lit (n2w n)] [p]) (fn_insts func) /\
    not_local_ptr cenv es.scopes p /\ n < dimword (:256) /\
    ~not_fresh_at sa p /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> p) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> p) /\
    ghost_inv d cenv cx es G tn s /\
    step_inst_base (mk_inst aid ALLOCA [Lit (n2w n)] [p]) s = OK u ==>
    ghost_inv d cenv cx es
      (step_prov PG G (mk_inst aid ALLOCA [Lit (n2w n)] [p]) u)
      (step_taint (mk_inst aid ALLOCA [Lit (n2w n)] [p]) s u tn) u /\
    ghost_kept cenv es sa G tn s
      (step_prov PG G (mk_inst aid ALLOCA [Lit (n2w n)] [p]) u)
      (step_taint (mk_inst aid ALLOCA [Lit (n2w n)] [p]) s u tn)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule annassign_alloca_ghost_inv_ptr >> metis_tac[]) >>
  irule annassign_alloca_ghost_kept_ptr >> metis_tac[]
QED
