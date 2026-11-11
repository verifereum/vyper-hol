Theory bodyPtrIfExpAllocGhost
Ancestors
  bodyPtrIfExpAllocLocals allocationPtr bodyPtrDefs ptrDiscipline decoderGhostFramePtr
  venomState venomInst finite_map compileEnv loweringStateRelDefs exprSimDefs exprLoweringProps

Theorem alloca_step_lookup_preserved:
  !s id n out u p.
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
    p <> out ==> lookup_var p u = lookup_var p s
Proof
  rpt strip_tac >>
  drule alloca_step_operand_preserved >>
  disch_then (qspec_then `Var p` mp_tac) >>
  simp[eval_operand_def]
QED

Theorem alloca_step_return_buf_ptr:
  !ctx fn cenv cx es s d G tn PG id n out u.
    stmt_state_rel ctx fn cenv cx es s /\
    return_buf_ptr d cenv G tn s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> out) ==>
    return_buf_ptr d cenv
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) u
Proof
  rpt gen_tac >> strip_tac >> Cases_on `d` >> simp[return_buf_ptr_def] >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  gvs[return_buf_ptr_def] >>
  `x <> out` by metis_tac[] >>
  drule_all alloca_step_lookup_preserved >> strip_tac >>
  simp[] >>
  irule alloca_step_old_ptr_covers >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem alloca_step_ghost_inv_separated:
  !ctx fn cenv cx es s d G tn PG id n out u.
    stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
    not_local_ptr cenv es.scopes out /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> out) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> out) ==>
    ghost_inv d cenv cx es
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) u
Proof
  rpt gen_tac >> strip_tac >>
  `state_rel fn cenv cx es s` by gvs[stmt_state_rel_def] >>
  qpat_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_inv_def] >> strip_tac >>
  rewrite_tac[ghost_inv_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `p <> out` by metis_tac[not_local_ptr_def] >>
      first_x_assum (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
      simp[] >> strip_tac >> conj_tac
      >- (irule alloca_step_old_ptr_covers >> simp[] >>
          goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      rpt gen_tac >> strip_tac >>
      drule_all alloca_step_lookup_preserved >> strip_tac >>
      `lookup_var p s = SOME w` by metis_tac[] >>
      drule_all alloca_step_local_robust >> simp[]) >>
  conj_tac
  >- (irule alloca_step_return_buf_ptr >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `x <> out` by metis_tac[] >>
      simp[step_taint_other_output, mk_inst_def] >> metis_tac[]) >>
  irule alloca_step_stor_taint_ok >> simp[] >> metis_tac[]
QED
