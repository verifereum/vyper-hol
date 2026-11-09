(* Allocation taint extension is disjoint from a placed value's footprint. *)
Theory assignBasePtrAllocSource
Ancestors assignBasePtrLiteralGhost robustCopyTransportPtr loweringPosts
  bodyPtrDefs venomState venomInst ptrDiscipline words pred_set allocationPtr

Theorem assign_base_ptr_alloca_placed_footprint:
  !ctx func cenv cx es s id n out t ty sa sb v op tv w i.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
    expr_val_at cenv cx ty sa sb es v op s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    eval_operand op s = SOME w /\
    w2n w <= i /\ i < w2n w + val_footprint tv v ==>
    i NOTIN new_site_bytes s t
Proof
  rpt gen_tac >> strip_tac >>
  fs[expr_val_at_def]
  >- (irule assign_base_ptr_alloca_old_taint_frame >> conj_tac
      >- (qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >> decide_tac) >>
      metis_tac[]) >>
  irule assign_base_ptr_alloca_local_taint_frame >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem assign_base_ptr_alloca_robust_source:
  !ctx func cenv cx es s id n out t ty sa sb v op tv w tn.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
    expr_val_at cenv cx ty sa sb es v op s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    eval_operand op s = SOME w /\ op <> Var out /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory tv v (w2n w) m) ==>
    eval_operand op t = SOME w /\
    (!m. mem_agree_outside
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_mem
      t.vs_memory m ==> val_in_memory tv v (w2n w) m)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_ptr_alloca_ghost_frame >>
  disch_then (qspecl_then [`[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
  conj_tac
  >- (drule alloca_step_operand_preserved >>
      disch_then (qspec_then `op` mp_tac) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- fs[expr_val_at_def] >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`s.vs_memory`, `tn.t_mem`, `new_site_bytes s t`] >>
  simp[] >> rpt strip_tac >>
  drule_all assign_base_ptr_alloca_placed_footprint >> simp[]
QED
