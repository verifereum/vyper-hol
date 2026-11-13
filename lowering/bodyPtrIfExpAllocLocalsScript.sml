Theory bodyPtrIfExpAllocLocals
Ancestors
  bodyPtrIfExpAllocFrame bodyPtrDefs compileEnv loweringStateRelDefs exprSimProps
  venomState venomInst ptrDiscipline finite_map

Theorem local_ptr_footprint_below_frontier:
  !fn cenv cx es s name entry p sz w.
    state_rel fn cenv cx es s /\
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (!i. w2n w <= i /\
         i < w2n w + val_footprint entry.type entry.value ==>
         i < s.vs_alloca_next)
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_rel fn cenv es.scopes s` by gvs[state_rel_def] >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
  simp[local_ptrs_rel_def] >> strip_tac >>
  first_x_assum (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  drule val_footprint_le >> strip_tac >> simp[] >> decide_tac
QED

(* The address is deliberately the pre-step address: out may alias p. *)
Theorem alloca_step_local_robust:
  !fn cenv cx es s d G tn name entry p sz w n id out u.
    state_rel fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\ n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
    !mem. mem_agree_outside
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_mem
      u.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n w) mem
Proof
  rpt gen_tac >> strip_tac >>
  drule_all local_ptr_footprint_below_frontier >> strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory entry.type entry.value (w2n w) mem` by
    (qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
     simp[ghost_inv_def] >> strip_tac >>
     first_x_assum (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
     simp[]) >>
  rpt strip_tac >> irule alloca_step_robust_below_frontier >>
  conj_tac >- simp[] >>
  qexistsl_tac [`id`, `n`, `out`, `s`, `u`, `tn`] >> simp[]
QED
