Theory bodyPtrIfExpNonwordFinish
Ancestors
  bodyPtrIfExpWordFinish bodyPtrIfExpAssignFrame bodyPtrDefs
  ptrDiscipline venomState venomInst finite_map
  loweringPosts vyperState stmtFragPtr exprSimPtrLiteralBuffer
  ghostPcTransportPtr exprSimIfExp exprSimDefs exprLowering vyperAST compileEnv loweringStateRelDefs

Theorem ifexp_assign_ptr_buf_ok:
  eval_operand src s = SOME w /\ ptr_buf_ok ce e src G s ==>
  ptr_buf_ok ce e (Var out)
    (step_prov PG G (mk_inst id ASSIGN [src] [out]) (update_var out w s))
    (update_var out w s)
Proof
  strip_tac >>
  qpat_x_assum `ptr_buf_ok _ _ _ _ _` mp_tac >>
  simp[ptr_buf_ok_def, assign_result_value] >> strip_tac >>
  rpt strip_tac >> first_x_assum drule >> simp[] >>
  strip_tac >> qexistsl_tac [`b`, `sz`] >>
  simp[SRULE [op_prov_def] assign_result_prov]
QED

Theorem ifexp_nonword_suffix_ghost:
  eval_operand op u = SOME w /\
  read_result cx tv ee = (INL v,ee) /\ ptr_val_ok cx t v op G tn u /\
  ptr_buf_ok ce e op G u /\
  ghost_inv d ce cx ee G tn u /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==> x <> rv) /\
  (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==> x <> rv) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> rv) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> rv) ==>
  ptr_vv_ok cx t tv (StackValue t (Var rv)) ee
    (step_prov PG G (mk_inst id ASSIGN [op] [rv]) (update_var rv w u))
    (step_taint (mk_inst id ASSIGN [op] [rv]) u (update_var rv w u) tn)
    (jump_to xl (update_var rv w u with vs_inst_idx := k)) /\
  ptr_buf_ok ce e (Var rv)
    (step_prov PG G (mk_inst id ASSIGN [op] [rv]) (update_var rv w u))
    (jump_to xl (update_var rv w u with vs_inst_idx := k)) /\
  ghost_inv d ce cx ee
    (step_prov PG G (mk_inst id ASSIGN [op] [rv]) (update_var rv w u))
    (step_taint (mk_inst id ASSIGN [op] [rv]) u (update_var rv w u) tn)
    (jump_to xl (update_var rv w u with vs_inst_idx := k)) /\
  ghost_kept ce es sa G0 tn0 s0
    (step_prov PG G (mk_inst id ASSIGN [op] [rv]) (update_var rv w u))
    (step_taint (mk_inst id ASSIGN [op] [rv]) u (update_var rv w u) tn)
Proof
  strip_tac >> conj_tac
  >- (simp[ptr_vv_ok_def] >>
      drule_all assign_ptr_val_ok >>
      disch_then (qspecl_then [`rv`, `id`, `PG`] mp_tac) >>
      simp[ptr_val_ok_def, ptr_mem_ok_def, jump_to_def, lookup_var_def]) >>
  conj_tac
  >- (drule_all ifexp_assign_ptr_buf_ok >>
      simp[ptr_buf_ok_def, jump_to_def, lookup_var_def]) >>
  conj_tac
  >- (simp[jump_to_def, ghost_inv_jump_to,
           SRULE [ghost_inv_gas_obs] literal_ptr_ghost_inv_normalize] >>
      irule assign_ghost_inv >> simp[] >> metis_tac[]) >>
  irule assign_ghost_kept >> simp[] >> metis_tac[]
QED
